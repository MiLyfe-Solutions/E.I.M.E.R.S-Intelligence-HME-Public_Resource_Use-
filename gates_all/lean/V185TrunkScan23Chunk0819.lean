import V185TrunkScan23Chunk0818

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4845654 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4845654 : Nat := 118140960795 + 4845654 * 2 ^ 59
def prefixEnd_4845654 : Nat := 4983230072969 + 3 ^ 40 * 4845654 * 2
def baseEnd_4845654 : Nat := 2488149587381689590140249

theorem tailTrace_4845654 : CollatzResearch.WordTrace tailWord_4845654 prefixEnd_4845654 2488149587381689590140249 := by
  unfold tailWord_4845654
  simp only [CollatzResearch.WordTrace]
  refine ⟨11045970049189412791372001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117823680524687069774634677 11045970049189412791372001)
  ·
    refine ⟨8284477536892059593529001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11045970049189412791372001 8284477536892059593529001)
    ·
      refine ⟨6213358152669044695146751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8284477536892059593529001 6213358152669044695146751)
      ·
        refine ⟨9320037229003567042720127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6213358152669044695146751 9320037229003567042720127)
        ·
          refine ⟨13980055843505350564080191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9320037229003567042720127 13980055843505350564080191)
          ·
            refine ⟨20970083765258025846120287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13980055843505350564080191 20970083765258025846120287)
            ·
              refine ⟨31455125647887038769180431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20970083765258025846120287 31455125647887038769180431)
              ·
                refine ⟨47182688471830558153770647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31455125647887038769180431 47182688471830558153770647)
                ·
                  refine ⟨70774032707745837230655971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47182688471830558153770647 70774032707745837230655971)
                  ·
                    refine ⟨106161049061618755845983957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70774032707745837230655971 106161049061618755845983957)
                    ·
                      refine ⟨2488149587381689590140249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106161049061618755845983957 2488149587381689590140249)
                      ·
                        rfl

theorem cell23_4845654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4845654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845654 prefixEnd_4845654 := by exact prefixLift 4845654
  have htrace : WordTrace (prefixWord ++ tailWord_4845654) baseStart_4845654 baseEnd_4845654 := by
    simpa [prefixWord, tailWord_4845654, baseEnd_4845654] using wordTrace_append hprefix tailTrace_4845654
  have hstable : (prefixWord ++ tailWord_4845654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845654).length < 2 ^ (prefixWord ++ tailWord_4845654).sum := by decide
  have hdescent : baseEnd_4845654 < baseStart_4845654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845704 : List Nat := [2, 1, 3, 4, 1, 2, 2, 2, 6]
def baseStart_4845704 : Nat := 118140960795 + 4845704 * 2 ^ 59
def prefixEnd_4845704 : Nat := 4983230072969 + 3 ^ 40 * 4845704 * 2
def baseEnd_4845704 : Nat := 276463917934934932723891

theorem tailTrace_4845704 : CollatzResearch.WordTrace tailWord_4845704 prefixEnd_4845704 276463917934934932723891 := by
  unfold tailWord_4845704
  simp only [CollatzResearch.WordTrace]
  refine ⟨88368672218424731600636083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117824896291232975467514777 88368672218424731600636083)
  ·
    refine ⟨132553008327637097400954125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88368672218424731600636083 132553008327637097400954125)
    ·
      refine ⟨49707378122863911525357797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132553008327637097400954125 49707378122863911525357797)
      ·
        refine ⟨9320133398036983411004587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49707378122863911525357797 9320133398036983411004587)
        ·
          refine ⟨13980200097055475116506881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9320133398036983411004587 13980200097055475116506881)
          ·
            refine ⟨10485150072791606337380161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13980200097055475116506881 10485150072791606337380161)
            ·
              refine ⟨7863862554593704753035121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10485150072791606337380161 7863862554593704753035121)
              ·
                refine ⟨5897896915945278564776341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7863862554593704753035121 5897896915945278564776341)
                ·
                  refine ⟨276463917934934932723891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5897896915945278564776341 276463917934934932723891)
                  ·
                    rfl

theorem cell23_4845704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 6].length) (baseStart_4845704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845704 prefixEnd_4845704 := by exact prefixLift 4845704
  have htrace : WordTrace (prefixWord ++ tailWord_4845704) baseStart_4845704 baseEnd_4845704 := by
    simpa [prefixWord, tailWord_4845704, baseEnd_4845704] using wordTrace_append hprefix tailTrace_4845704
  have hstable : (prefixWord ++ tailWord_4845704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845704).length < 2 ^ (prefixWord ++ tailWord_4845704).sum := by decide
  have hdescent : baseEnd_4845704 < baseStart_4845704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845707 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 5, 5, 2]
def baseStart_4845707 : Nat := 118140960795 + 4845707 * 2 ^ 59
def prefixEnd_4845707 : Nat := 4983230072969 + 3 ^ 40 * 4845707 * 2
def baseEnd_4845707 : Nat := 2488176801856377882777505

theorem tailTrace_4845707 : CollatzResearch.WordTrace tailWord_4845707 prefixEnd_4845707 2488176801856377882777505 := by
  unfold tailWord_4845707
  simp only [CollatzResearch.WordTrace]
  refine ⟨176737453855838594713631375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117824969237225729809087583 176737453855838594713631375)
  ·
    refine ⟨265106180783757892070447063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176737453855838594713631375 265106180783757892070447063)
    ·
      refine ⟨397659271175636838105670595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265106180783757892070447063 397659271175636838105670595)
      ·
        refine ⟨596488906763455257158505893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397659271175636838105670595 596488906763455257158505893)
        ·
          refine ⟨111841670018147860717219855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 596488906763455257158505893 111841670018147860717219855)
          ·
            refine ⟨167762505027221791075829783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111841670018147860717219855 167762505027221791075829783)
            ·
              refine ⟨251643757540832686613744675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167762505027221791075829783 251643757540832686613744675)
              ·
                refine ⟨377465636311249029920617013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251643757540832686613744675 377465636311249029920617013)
                ·
                  refine ⟨35387403404179596555057845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 377465636311249029920617013 35387403404179596555057845)
                  ·
                    refine ⟨3317569069141837177036673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35387403404179596555057845 3317569069141837177036673)
                    ·
                      refine ⟨2488176801856377882777505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317569069141837177036673 2488176801856377882777505)
                      ·
                        rfl

theorem cell23_4845707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 5, 2].length) (baseStart_4845707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845707 prefixEnd_4845707 := by exact prefixLift 4845707
  have htrace : WordTrace (prefixWord ++ tailWord_4845707) baseStart_4845707 baseEnd_4845707 := by
    simpa [prefixWord, tailWord_4845707, baseEnd_4845707] using wordTrace_append hprefix tailTrace_4845707
  have hstable : (prefixWord ++ tailWord_4845707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845707).length < 2 ^ (prefixWord ++ tailWord_4845707).sum := by decide
  have hdescent : baseEnd_4845707 < baseStart_4845707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845724 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_4845724 : Nat := 118140960795 + 4845724 * 2 ^ 59
def prefixEnd_4845724 : Nat := 4983230072969 + 3 ^ 40 * 4845724 * 2
def baseEnd_4845724 : Nat := 2488185531027504316264927

theorem tailTrace_4845724 : CollatzResearch.WordTrace tailWord_4845724 prefixEnd_4845724 2488185531027504316264927 := by
  unfold tailWord_4845724
  simp only [CollatzResearch.WordTrace]
  refine ⟨88369036948388503308500113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117825382597851337744666817 88369036948388503308500113)
  ·
    refine ⟨66276777711291377481375085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88369036948388503308500113 66276777711291377481375085)
    ·
      refine ⟨24853791641734266555515657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66276777711291377481375085 24853791641734266555515657)
      ·
        refine ⟨18640343731300699916636743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24853791641734266555515657 18640343731300699916636743)
        ·
          refine ⟨27960515596951049874955115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18640343731300699916636743 27960515596951049874955115)
          ·
            refine ⟨41940773395426574812432673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27960515596951049874955115 41940773395426574812432673)
            ·
              refine ⟨31455580046569931109324505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41940773395426574812432673 31455580046569931109324505)
              ·
                refine ⟨23591685034927448331993379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31455580046569931109324505 23591685034927448331993379)
                ·
                  refine ⟨35387527552391172497990069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23591685034927448331993379 35387527552391172497990069)
                  ·
                    refine ⟨3317580708036672421686569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35387527552391172497990069 3317580708036672421686569)
                    ·
                      refine ⟨2488185531027504316264927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317580708036672421686569 2488185531027504316264927)
                      ·
                        rfl

theorem cell23_4845724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_4845724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845724 prefixEnd_4845724 := by exact prefixLift 4845724
  have htrace : WordTrace (prefixWord ++ tailWord_4845724) baseStart_4845724 baseEnd_4845724 := by
    simpa [prefixWord, tailWord_4845724, baseEnd_4845724] using wordTrace_append hprefix tailTrace_4845724
  have hstable : (prefixWord ++ tailWord_4845724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845724).length < 2 ^ (prefixWord ++ tailWord_4845724).sum := by decide
  have hdescent : baseEnd_4845724 < baseStart_4845724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845741 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_4845741 : Nat := 118140960795 + 4845741 * 2 ^ 59
def prefixEnd_4845741 : Nat := 4983230072969 + 3 ^ 40 * 4845741 * 2
def baseEnd_4845741 : Nat := 2488194260198630749752349

theorem tailTrace_4845741 : CollatzResearch.WordTrace tailWord_4845741 prefixEnd_4845741 2488194260198630749752349 := by
  unfold tailWord_4845741
  simp only [CollatzResearch.WordTrace]
  refine ⟨176738693937715418520369077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117825795958476945680246051 176738693937715418520369077)
  ·
    refine ⟨16569252556660820486284601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176738693937715418520369077 16569252556660820486284601)
    ·
      refine ⟨12426939417495615364713451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16569252556660820486284601 12426939417495615364713451)
      ·
        refine ⟨18640409126243423047070177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12426939417495615364713451 18640409126243423047070177)
        ·
          refine ⟨13980306844682567285302633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18640409126243423047070177 13980306844682567285302633)
          ·
            refine ⟨10485230133511925463976975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13980306844682567285302633 10485230133511925463976975)
            ·
              refine ⟨15727845200267888195965463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10485230133511925463976975 15727845200267888195965463)
              ·
                refine ⟨23591767800401832293948195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15727845200267888195965463 23591767800401832293948195)
                ·
                  refine ⟨35387651700602748440922293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23591767800401832293948195 35387651700602748440922293)
                  ·
                    refine ⟨3317592346931507666336465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35387651700602748440922293 3317592346931507666336465)
                    ·
                      refine ⟨2488194260198630749752349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317592346931507666336465 2488194260198630749752349)
                      ·
                        rfl

theorem cell23_4845741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_4845741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845741 prefixEnd_4845741 := by exact prefixLift 4845741
  have htrace : WordTrace (prefixWord ++ tailWord_4845741) baseStart_4845741 baseEnd_4845741 := by
    simpa [prefixWord, tailWord_4845741, baseEnd_4845741] using wordTrace_append hprefix tailTrace_4845741
  have hstable : (prefixWord ++ tailWord_4845741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845741).length < 2 ^ (prefixWord ++ tailWord_4845741).sum := by decide
  have hdescent : baseEnd_4845741 < baseStart_4845741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845747 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 4, 4]
def baseStart_4845747 : Nat := 118140960795 + 4845747 * 2 ^ 59
def prefixEnd_4845747 : Nat := 4983230072969 + 3 ^ 40 * 4845747 * 2
def baseEnd_4845747 : Nat := 829399113694185908759107

theorem tailTrace_4845747 : CollatzResearch.WordTrace tailWord_4845747 prefixEnd_4845747 829399113694185908759107 := by
  unfold tailWord_4845747
  simp only [CollatzResearch.WordTrace]
  refine ⟨176738912775693681545087495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117825941850462454363391663 176738912775693681545087495)
  ·
    refine ⟨265108369163540522317631243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176738912775693681545087495 265108369163540522317631243)
    ·
      refine ⟨397662553745310783476446865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265108369163540522317631243 397662553745310783476446865)
      ·
        refine ⟨298246915308983087607335149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397662553745310783476446865 298246915308983087607335149)
        ·
          refine ⟨111842593240868657852750681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 298246915308983087607335149 111842593240868657852750681)
          ·
            refine ⟨83881944930651493389563011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111842593240868657852750681 83881944930651493389563011)
            ·
              refine ⟨125822917395977240084344517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83881944930651493389563011 125822917395977240084344517)
              ·
                refine ⟨23591797011745732515814597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125822917395977240084344517 23591797011745732515814597)
                ·
                  refine ⟨4423461939702324846715237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23591797011745732515814597 4423461939702324846715237)
                  ·
                    refine ⟨829399113694185908759107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4423461939702324846715237 829399113694185908759107)
                    ·
                      rfl

theorem cell23_4845747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 4].length) (baseStart_4845747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845747 prefixEnd_4845747 := by exact prefixLift 4845747
  have htrace : WordTrace (prefixWord ++ tailWord_4845747) baseStart_4845747 baseEnd_4845747 := by
    simpa [prefixWord, tailWord_4845747, baseEnd_4845747] using wordTrace_append hprefix tailTrace_4845747
  have hstable : (prefixWord ++ tailWord_4845747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845747).length < 2 ^ (prefixWord ++ tailWord_4845747).sum := by decide
  have hdescent : baseEnd_4845747 < baseStart_4845747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845751 : List Nat := [1, 1, 3, 1, 4, 4, 2, 1, 1, 5]
def baseStart_4845751 : Nat := 118140960795 + 4845751 * 2 ^ 59
def prefixEnd_4845751 : Nat := 4983230072969 + 3 ^ 40 * 4845751 * 2
def baseEnd_4845751 : Nat := 829399798335058570209101

theorem tailTrace_4845751 : CollatzResearch.WordTrace tailWord_4845751 prefixEnd_4845751 829399798335058570209101 := by
  unfold tailWord_4845751
  simp only [CollatzResearch.WordTrace]
  refine ⟨176739058667679190228233107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117826039111786126818822071 176739058667679190228233107)
  ·
    refine ⟨265108588001518785342349661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176739058667679190228233107 265108588001518785342349661)
    ·
      refine ⟨99415720500569544503381123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265108588001518785342349661 99415720500569544503381123)
      ·
        refine ⟨149123580750854316755071685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99415720500569544503381123 149123580750854316755071685)
        ·
          refine ⟨27960671390785184391575941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149123580750854316755071685 27960671390785184391575941)
          ·
            refine ⟨5242625885772222073420489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27960671390785184391575941 5242625885772222073420489)
            ·
              refine ⟨3931969414329166555065367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5242625885772222073420489 3931969414329166555065367)
              ·
                refine ⟨5897954121493749832598051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3931969414329166555065367 5897954121493749832598051)
                ·
                  refine ⟨8846931182240624748897077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5897954121493749832598051 8846931182240624748897077)
                  ·
                    refine ⟨829399798335058570209101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8846931182240624748897077 829399798335058570209101)
                    ·
                      rfl

theorem cell23_4845751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 1, 5].length) (baseStart_4845751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845751 prefixEnd_4845751 := by exact prefixLift 4845751
  have htrace : WordTrace (prefixWord ++ tailWord_4845751) baseStart_4845751 baseEnd_4845751 := by
    simpa [prefixWord, tailWord_4845751, baseEnd_4845751] using wordTrace_append hprefix tailTrace_4845751
  have hstable : (prefixWord ++ tailWord_4845751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845751).length < 2 ^ (prefixWord ++ tailWord_4845751).sum := by decide
  have hdescent : baseEnd_4845751 < baseStart_4845751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845757 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_4845757 : Nat := 118140960795 + 4845757 * 2 ^ 59
def prefixEnd_4845757 : Nat := 4983230072969 + 3 ^ 40 * 4845757 * 2
def baseEnd_4845757 : Nat := 2488202475889102687152275

theorem tailTrace_4845757 : CollatzResearch.WordTrace tailWord_4845757 prefixEnd_4845757 2488202475889102687152275 := by
  unfold tailWord_4845757
  simp only [CollatzResearch.WordTrace]
  refine ⟨176739277505657453252951525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117826185003771635501967683 176739277505657453252951525)
  ·
    refine ⟨33138614532310772484928411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176739277505657453252951525 33138614532310772484928411)
    ·
      refine ⟨49707921798466158727392617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33138614532310772484928411 49707921798466158727392617)
      ·
        refine ⟨37280941348849619045544463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49707921798466158727392617 37280941348849619045544463)
        ·
          refine ⟨55921412023274428568316695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37280941348849619045544463 55921412023274428568316695)
          ·
            refine ⟨83882118034911642852475043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55921412023274428568316695 83882118034911642852475043)
            ·
              refine ⟨125823177052367464278712565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83882118034911642852475043 125823177052367464278712565)
              ·
                refine ⟨11795922848659449776129303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125823177052367464278712565 11795922848659449776129303)
                ·
                  refine ⟨17693884272989174664193955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11795922848659449776129303 17693884272989174664193955)
                  ·
                    refine ⟨26540826409483761996290933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17693884272989174664193955 26540826409483761996290933)
                    ·
                      refine ⟨2488202475889102687152275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26540826409483761996290933 2488202475889102687152275)
                      ·
                        rfl

theorem cell23_4845757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_4845757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845757 prefixEnd_4845757 := by exact prefixLift 4845757
  have htrace : WordTrace (prefixWord ++ tailWord_4845757) baseStart_4845757 baseEnd_4845757 := by
    simpa [prefixWord, tailWord_4845757, baseEnd_4845757] using wordTrace_append hprefix tailTrace_4845757
  have hstable : (prefixWord ++ tailWord_4845757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845757).length < 2 ^ (prefixWord ++ tailWord_4845757).sum := by decide
  have hdescent : baseEnd_4845757 < baseStart_4845757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845771 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 3, 2, 2]
def baseStart_4845771 : Nat := 118140960795 + 4845771 * 2 ^ 59
def prefixEnd_4845771 : Nat := 4983230072969 + 3 ^ 40 * 4845771 * 2
def baseEnd_4845771 : Nat := 2488209664618265632377211

theorem tailTrace_4845771 : CollatzResearch.WordTrace tailWord_4845771 prefixEnd_4845771 2488209664618265632377211 := by
  unfold tailWord_4845771
  simp only [CollatzResearch.WordTrace]
  refine ⟨176739788127606733643961167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117826525418404489095974111 176739788127606733643961167)
  ·
    refine ⟨265109682191410100465941751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176739788127606733643961167 265109682191410100465941751)
    ·
      refine ⟨397664523287115150698912627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265109682191410100465941751 397664523287115150698912627)
      ·
        refine ⟨596496784930672726048368941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397664523287115150698912627 596496784930672726048368941)
        ·
          refine ⟨223686294349002272268138353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 596496784930672726048368941 223686294349002272268138353)
          ·
            refine ⟨167764720761751704201103765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223686294349002272268138353 167764720761751704201103765)
            ·
              refine ⟨7863971285707111134426739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 167764720761751704201103765 7863971285707111134426739)
              ·
                refine ⟨11795956928560666701640109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7863971285707111134426739 11795956928560666701640109)
                ·
                  refine ⟨4423483848210250013115041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11795956928560666701640109 4423483848210250013115041)
                  ·
                    refine ⟨3317612886157687509836281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4423483848210250013115041 3317612886157687509836281)
                    ·
                      refine ⟨2488209664618265632377211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317612886157687509836281 2488209664618265632377211)
                      ·
                        rfl

theorem cell23_4845771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 2, 2].length) (baseStart_4845771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845771 prefixEnd_4845771 := by exact prefixLift 4845771
  have htrace : WordTrace (prefixWord ++ tailWord_4845771) baseStart_4845771 baseEnd_4845771 := by
    simpa [prefixWord, tailWord_4845771, baseEnd_4845771] using wordTrace_append hprefix tailTrace_4845771
  have hstable : (prefixWord ++ tailWord_4845771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845771).length < 2 ^ (prefixWord ++ tailWord_4845771).sum := by decide
  have hdescent : baseEnd_4845771 < baseStart_4845771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845774 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_4845774 : Nat := 118140960795 + 4845774 * 2 ^ 59
def prefixEnd_4845774 : Nat := 4983230072969 + 3 ^ 40 * 4845774 * 2
def baseEnd_4845774 : Nat := 2488211205060229120639697

theorem tailTrace_4845774 : CollatzResearch.WordTrace tailWord_4845774 prefixEnd_4845774 2488211205060229120639697 := by
  unfold tailWord_4845774
  simp only [CollatzResearch.WordTrace]
  refine ⟨22092487193324483144540047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117826598364397243437546917 22092487193324483144540047)
  ·
    refine ⟨33138730789986724716810071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22092487193324483144540047 33138730789986724716810071)
    ·
      refine ⟨49708096184980087075215107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33138730789986724716810071 49708096184980087075215107)
      ·
        refine ⟨74562144277470130612822661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49708096184980087075215107 74562144277470130612822661)
        ·
          refine ⟨13980402052025649489904249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74562144277470130612822661 13980402052025649489904249)
          ·
            refine ⟨10485301539019237117428187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13980402052025649489904249 10485301539019237117428187)
            ·
              refine ⟨15727952308528855676142281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10485301539019237117428187 15727952308528855676142281)
              ·
                refine ⟨11795964231396641757106711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15727952308528855676142281 11795964231396641757106711)
                ·
                  refine ⟨17693946347094962635660067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11795964231396641757106711 17693946347094962635660067)
                  ·
                    refine ⟨26540919520642443953490101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17693946347094962635660067 26540919520642443953490101)
                    ·
                      refine ⟨2488211205060229120639697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26540919520642443953490101 2488211205060229120639697)
                      ·
                        rfl

theorem cell23_4845774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_4845774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845774 prefixEnd_4845774 := by exact prefixLift 4845774
  have htrace : WordTrace (prefixWord ++ tailWord_4845774) baseStart_4845774 baseEnd_4845774 := by
    simpa [prefixWord, tailWord_4845774, baseEnd_4845774] using wordTrace_append hprefix tailTrace_4845774
  have hstable : (prefixWord ++ tailWord_4845774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845774).length < 2 ^ (prefixWord ++ tailWord_4845774).sum := by decide
  have hdescent : baseEnd_4845774 < baseStart_4845774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845781 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 1, 6]
def baseStart_4845781 : Nat := 118140960795 + 4845781 * 2 ^ 59
def prefixEnd_4845781 : Nat := 4983230072969 + 3 ^ 40 * 4845781 * 2
def baseEnd_4845781 : Nat := 829404933141603531084055

theorem tailTrace_4845781 : CollatzResearch.WordTrace tailWord_4845781 prefixEnd_4845781 829404933141603531084055 := by
  unfold tailWord_4845781
  simp only [CollatzResearch.WordTrace]
  refine ⟨176740152857570505351825197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117826768571713670234550131 176740152857570505351825197)
  ·
    refine ⟨66277557321588939506934449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176740152857570505351825197 66277557321588939506934449)
    ·
      refine ⟨49708167991191704630200837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66277557321588939506934449 49708167991191704630200837)
      ·
        refine ⟨9320281498348444618162657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49708167991191704630200837 9320281498348444618162657)
        ·
          refine ⟨6990211123761333463621993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9320281498348444618162657 6990211123761333463621993)
          ·
            refine ⟨5242658342821000097716495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6990211123761333463621993 5242658342821000097716495)
            ·
              refine ⟨7863987514231500146574743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5242658342821000097716495 7863987514231500146574743)
              ·
                refine ⟨11795981271347250219862115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7863987514231500146574743 11795981271347250219862115)
                ·
                  refine ⟨17693971907020875329793173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11795981271347250219862115 17693971907020875329793173)
                  ·
                    refine ⟨829404933141603531084055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17693971907020875329793173 829404933141603531084055)
                    ·
                      rfl

theorem cell23_4845781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_4845781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845781 prefixEnd_4845781 := by exact prefixLift 4845781
  have htrace : WordTrace (prefixWord ++ tailWord_4845781) baseStart_4845781 baseEnd_4845781 := by
    simpa [prefixWord, tailWord_4845781, baseEnd_4845781] using wordTrace_append hprefix tailTrace_4845781
  have hstable : (prefixWord ++ tailWord_4845781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845781).length < 2 ^ (prefixWord ++ tailWord_4845781).sum := by decide
  have hdescent : baseEnd_4845781 < baseStart_4845781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845784 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 1, 2, 4]
def baseStart_4845784 : Nat := 118140960795 + 4845784 * 2 ^ 59
def prefixEnd_4845784 : Nat := 4983230072969 + 3 ^ 40 * 4845784 * 2
def baseEnd_4845784 : Nat := 2488216339866774081514651

theorem tailTrace_4845784 : CollatzResearch.WordTrace tailWord_4845784 prefixEnd_4845784 2488216339866774081514651 := by
  unfold tailWord_4845784
  simp only [CollatzResearch.WordTrace]
  refine ⟨88370131138279818432092203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117826841517706424576122937 88370131138279818432092203)
  ·
    refine ⟨132555196707419727648138305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88370131138279818432092203 132555196707419727648138305)
    ·
      refine ⟨99416397530564795736103729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132555196707419727648138305 99416397530564795736103729)
      ·
        refine ⟨74562298147923596802077797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99416397530564795736103729 74562298147923596802077797)
        ·
          refine ⟨13980430902735674400389587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74562298147923596802077797 13980430902735674400389587)
          ·
            refine ⟨20970646354103511600584381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13980430902735674400389587 20970646354103511600584381)
            ·
              refine ⟨7863992382788816850219143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20970646354103511600584381 7863992382788816850219143)
              ·
                refine ⟨11795988574183225275328715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7863992382788816850219143 11795988574183225275328715)
                ·
                  refine ⟨17693982861274837912993073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11795988574183225275328715 17693982861274837912993073)
                  ·
                    refine ⟨13270487145956128434744805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17693982861274837912993073 13270487145956128434744805)
                    ·
                      refine ⟨2488216339866774081514651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13270487145956128434744805 2488216339866774081514651)
                      ·
                        rfl

theorem cell23_4845784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_4845784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845784 prefixEnd_4845784 := by exact prefixLift 4845784
  have htrace : WordTrace (prefixWord ++ tailWord_4845784) baseStart_4845784 baseEnd_4845784 := by
    simpa [prefixWord, tailWord_4845784, baseEnd_4845784] using wordTrace_append hprefix tailTrace_4845784
  have hstable : (prefixWord ++ tailWord_4845784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845784).length < 2 ^ (prefixWord ++ tailWord_4845784).sum := by decide
  have hdescent : baseEnd_4845784 < baseStart_4845784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845804 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 3]
def baseStart_4845804 : Nat := 118140960795 + 4845804 * 2 ^ 59
def prefixEnd_4845804 : Nat := 4983230072969 + 3 ^ 40 * 4845804 * 2
def baseEnd_4845804 : Nat := 2488226609479864003264559

theorem tailTrace_4845804 : CollatzResearch.WordTrace tailWord_4845804 prefixEnd_4845804 2488226609479864003264559 := by
  unfold tailWord_4845804
  simp only [CollatzResearch.WordTrace]
  refine ⟨88370495868243590139956233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117827327824324786853274977 88370495868243590139956233)
  ·
    refine ⟨66277871901182692604967175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88370495868243590139956233 66277871901182692604967175)
    ·
      refine ⟨99416807851774038907450763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66277871901182692604967175 99416807851774038907450763)
      ·
        refine ⟨149125211777661058361176145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99416807851774038907450763 149125211777661058361176145)
        ·
          refine ⟨111843908833245793770882109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149125211777661058361176145 111843908833245793770882109)
          ·
            refine ⟨41941465812467172664080791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111843908833245793770882109 41941465812467172664080791)
            ·
              refine ⟨62912198718700758996121187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41941465812467172664080791 62912198718700758996121187)
              ·
                refine ⟨94368298078051138494181781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62912198718700758996121187 94368298078051138494181781)
                ·
                  refine ⟨4423513972408647116914771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94368298078051138494181781 4423513972408647116914771)
                  ·
                    refine ⟨6635270958612970675372157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4423513972408647116914771 6635270958612970675372157)
                    ·
                      refine ⟨2488226609479864003264559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6635270958612970675372157 2488226609479864003264559)
                      ·
                        rfl

theorem cell23_4845804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_4845804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845804 prefixEnd_4845804 := by exact prefixLift 4845804
  have htrace : WordTrace (prefixWord ++ tailWord_4845804) baseStart_4845804 baseEnd_4845804 := by
    simpa [prefixWord, tailWord_4845804, baseEnd_4845804] using wordTrace_append hprefix tailTrace_4845804
  have hstable : (prefixWord ++ tailWord_4845804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845804).length < 2 ^ (prefixWord ++ tailWord_4845804).sum := by decide
  have hdescent : baseEnd_4845804 < baseStart_4845804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845822 : List Nat := [4, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_4845822 : Nat := 118140960795 + 4845822 * 2 ^ 59
def prefixEnd_4845822 : Nat := 4983230072969 + 3 ^ 40 * 4845822 * 2
def baseEnd_4845822 : Nat := 2488235852131644932839477

theorem tailTrace_4845822 : CollatzResearch.WordTrace tailWord_4845822 prefixEnd_4845822 2488235852131644932839477 := by
  unfold tailWord_4845822
  simp only [CollatzResearch.WordTrace]
  refine ⟨22092706031302746169258465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117827765500281312902711813 22092706031302746169258465)
  ·
    refine ⟨16569529523477059626943849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22092706031302746169258465 16569529523477059626943849)
    ·
      refine ⟨12427147142607794720207887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16569529523477059626943849 12427147142607794720207887)
      ·
        refine ⟨18640720713911692080311831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12427147142607794720207887 18640720713911692080311831)
        ·
          refine ⟨27961081070867538120467747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18640720713911692080311831 27961081070867538120467747)
          ·
            refine ⟨41941621606301307180701621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27961081070867538120467747 41941621606301307180701621)
            ·
              refine ⟨3932027025590747548190777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41941621606301307180701621 3932027025590747548190777)
              ·
                refine ⟨2949020269193060661143083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3932027025590747548190777 2949020269193060661143083)
                ·
                  refine ⟨4423530403789590991714625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2949020269193060661143083 4423530403789590991714625)
                  ·
                    refine ⟨3317647802842193243785969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4423530403789590991714625 3317647802842193243785969)
                    ·
                      refine ⟨2488235852131644932839477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317647802842193243785969 2488235852131644932839477)
                      ·
                        rfl

theorem cell23_4845822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_4845822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845822 prefixEnd_4845822 := by exact prefixLift 4845822
  have htrace : WordTrace (prefixWord ++ tailWord_4845822) baseStart_4845822 baseEnd_4845822 := by
    simpa [prefixWord, tailWord_4845822, baseEnd_4845822] using wordTrace_append hprefix tailTrace_4845822
  have hstable : (prefixWord ++ tailWord_4845822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845822).length < 2 ^ (prefixWord ++ tailWord_4845822).sum := by decide
  have hdescent : baseEnd_4845822 < baseStart_4845822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845827 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 4]
def baseStart_4845827 : Nat := 118140960795 + 4845827 * 2 ^ 59
def prefixEnd_4845827 : Nat := 4983230072969 + 3 ^ 40 * 4845827 * 2
def baseEnd_4845827 : Nat := 2488238419534917413276953

theorem tailTrace_4845827 : CollatzResearch.WordTrace tailWord_4845827 prefixEnd_4845827 2488238419534917413276953 := by
  unfold tailWord_4845827
  simp only [CollatzResearch.WordTrace]
  refine ⟨176741830615403855207999735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117827887076935903471999823 176741830615403855207999735)
  ·
    refine ⟨265112745923105782811999603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176741830615403855207999735 265112745923105782811999603)
    ·
      refine ⟨397669118884658674217999405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265112745923105782811999603 397669118884658674217999405)
      ·
        refine ⟨149125919581747002831749777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 397669118884658674217999405 149125919581747002831749777)
        ·
          refine ⟨111844439686310252123812333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149125919581747002831749777 111844439686310252123812333)
          ·
            refine ⟨41941664882366344546429625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111844439686310252123812333 41941664882366344546429625)
            ·
              refine ⟨31456248661774758409822219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41941664882366344546429625 31456248661774758409822219)
              ·
                refine ⟨47184372992662137614733329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31456248661774758409822219 47184372992662137614733329)
                ·
                  refine ⟨35388279744496603211049997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47184372992662137614733329 35388279744496603211049997)
                  ·
                    refine ⟨13270604904186226204143749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35388279744496603211049997 13270604904186226204143749)
                    ·
                      refine ⟨2488238419534917413276953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13270604904186226204143749 2488238419534917413276953)
                      ·
                        rfl

theorem cell23_4845827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_4845827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845827 prefixEnd_4845827 := by exact prefixLift 4845827
  have htrace : WordTrace (prefixWord ++ tailWord_4845827) baseStart_4845827 baseEnd_4845827 := by
    simpa [prefixWord, tailWord_4845827, baseEnd_4845827] using wordTrace_append hprefix tailTrace_4845827
  have hstable : (prefixWord ++ tailWord_4845827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845827).length < 2 ^ (prefixWord ++ tailWord_4845827).sum := by decide
  have hdescent : baseEnd_4845827 < baseStart_4845827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845897 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 1, 7]
def baseStart_4845897 : Nat := 118140960795 + 4845897 * 2 ^ 59
def prefixEnd_4845897 : Nat := 4983230072969 + 3 ^ 40 * 4845897 * 2
def baseEnd_4845897 : Nat := 829424787726910713133877

theorem tailTrace_4845897 : CollatzResearch.WordTrace tailWord_4845897 prefixEnd_4845897 829424787726910713133877 := by
  unfold tailWord_4845897
  simp only [CollatzResearch.WordTrace]
  refine ⟨176744383725150257163047945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117829589150100171442031963 176744383725150257163047945)
  ·
    refine ⟨132558287793862692872285959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176744383725150257163047945 132558287793862692872285959)
    ·
      refine ⟨198837431690794039308428939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132558287793862692872285959 198837431690794039308428939)
      ·
        refine ⟨298256147536191058962643409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198837431690794039308428939 298256147536191058962643409)
        ·
          refine ⟨223692110652143294221982557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298256147536191058962643409 223692110652143294221982557)
          ·
            refine ⟨83884541494553735333243459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223692110652143294221982557 83884541494553735333243459)
            ·
              refine ⟨125826812241830602999865189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83884541494553735333243459 125826812241830602999865189)
              ·
                refine ⟨23592527295343238062474723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125826812241830602999865189 23592527295343238062474723)
                ·
                  refine ⟨35388790943014857093712085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23592527295343238062474723 35388790943014857093712085)
                  ·
                    refine ⟨829424787726910713133877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35388790943014857093712085 829424787726910713133877)
                    ·
                      rfl

theorem cell23_4845897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_4845897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845897 prefixEnd_4845897 := by exact prefixLift 4845897
  have htrace : WordTrace (prefixWord ++ tailWord_4845897) baseStart_4845897 baseEnd_4845897 := by
    simpa [prefixWord, tailWord_4845897, baseEnd_4845897] using wordTrace_append hprefix tailTrace_4845897
  have hstable : (prefixWord ++ tailWord_4845897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845897).length < 2 ^ (prefixWord ++ tailWord_4845897).sum := by decide
  have hdescent : baseEnd_4845897 < baseStart_4845897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845907 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 5]
def baseStart_4845907 : Nat := 118140960795 + 4845907 * 2 ^ 59
def prefixEnd_4845907 : Nat := 4983230072969 + 3 ^ 40 * 4845907 * 2
def baseEnd_4845907 : Nat := 2488279497987277100276585

theorem tailTrace_4845907 : CollatzResearch.WordTrace tailWord_4845907 prefixEnd_4845907 2488279497987277100276585 := by
  unfold tailWord_4845907
  simp only [CollatzResearch.WordTrace]
  refine ⟨176744748455114028870911975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117829832303409352580607983 176744748455114028870911975)
  ·
    refine ⟨265117122682671043306367963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176744748455114028870911975 265117122682671043306367963)
    ·
      refine ⟨397675684024006564959551945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265117122682671043306367963 397675684024006564959551945)
      ·
        refine ⟨298256763018004923719663959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397675684024006564959551945 298256763018004923719663959)
        ·
          refine ⟨447385144527007385579495939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298256763018004923719663959 447385144527007385579495939)
          ·
            refine ⟨671077716790511078369243909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447385144527007385579495939 671077716790511078369243909)
            ·
              refine ⟨125827071898220827194233233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 671077716790511078369243909 125827071898220827194233233)
              ·
                refine ⟨94370303923665620395674925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125827071898220827194233233 94370303923665620395674925)
                ·
                  refine ⟨35388863971374607648378097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94370303923665620395674925 35388863971374607648378097)
                  ·
                    refine ⟨26541647978530955736283573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35388863971374607648378097 26541647978530955736283573)
                    ·
                      refine ⟨2488279497987277100276585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26541647978530955736283573 2488279497987277100276585)
                      ·
                        rfl

theorem cell23_4845907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_4845907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845907 prefixEnd_4845907 := by exact prefixLift 4845907
  have htrace : WordTrace (prefixWord ++ tailWord_4845907) baseStart_4845907 baseEnd_4845907 := by
    simpa [prefixWord, tailWord_4845907, baseEnd_4845907] using wordTrace_append hprefix tailTrace_4845907
  have hstable : (prefixWord ++ tailWord_4845907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845907).length < 2 ^ (prefixWord ++ tailWord_4845907).sum := by decide
  have hdescent : baseEnd_4845907 < baseStart_4845907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845961 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 3, 4]
def baseStart_4845961 : Nat := 118140960795 + 4845961 * 2 ^ 59
def prefixEnd_4845961 : Nat := 4983230072969 + 3 ^ 40 * 4845961 * 2
def baseEnd_4845961 : Nat := 829435741980873296333779

theorem tailTrace_4845961 : CollatzResearch.WordTrace tailWord_4845961 prefixEnd_4845961 829435741980873296333779 := by
  unfold tailWord_4845961
  simp only [CollatzResearch.WordTrace]
  refine ⟨176746717996918396093377737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117831145331278930728918491 176746717996918396093377737)
  ·
    refine ⟨132560038497688797070033303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176746717996918396093377737 132560038497688797070033303)
    ·
      refine ⟨198840057746533195605049955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132560038497688797070033303 198840057746533195605049955)
      ·
        refine ⟨298260086619799793407574933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198840057746533195605049955 298260086619799793407574933)
        ·
          refine ⟨13980941560303115315980075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 298260086619799793407574933 13980941560303115315980075)
          ·
            refine ⟨20971412340454672973970113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13980941560303115315980075 20971412340454672973970113)
            ·
              refine ⟨15728559255341004730477585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20971412340454672973970113 15728559255341004730477585)
              ·
                refine ⟨11796419441505753547858189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15728559255341004730477585 11796419441505753547858189)
                ·
                  refine ⟨4423657290564657580446821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11796419441505753547858189 4423657290564657580446821)
                  ·
                    refine ⟨829435741980873296333779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4423657290564657580446821 829435741980873296333779)
                    ·
                      rfl

theorem cell23_4845961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 4].length) (baseStart_4845961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845961 prefixEnd_4845961 := by exact prefixLift 4845961
  have htrace : WordTrace (prefixWord ++ tailWord_4845961) baseStart_4845961 baseEnd_4845961 := by
    simpa [prefixWord, tailWord_4845961, baseEnd_4845961] using wordTrace_append hprefix tailTrace_4845961
  have hstable : (prefixWord ++ tailWord_4845961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845961).length < 2 ^ (prefixWord ++ tailWord_4845961).sum := by decide
  have hdescent : baseEnd_4845961 < baseStart_4845961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846086 : List Nat := [6, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_4846086 : Nat := 118140960795 + 4846086 * 2 ^ 59
def prefixEnd_4846086 : Nat := 4983230072969 + 3 ^ 40 * 4846086 * 2
def baseEnd_4846086 : Nat := 2488371411024431899938263

theorem tailTrace_4846086 : CollatzResearch.WordTrace tailWord_4846086 prefixEnd_4846086 2488371411024431899938263 := by
  unfold tailWord_4846086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5523477410045798201302441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 117834184747643694961118741 5523477410045798201302441)
  ·
    refine ⟨4142608057534348650976831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5523477410045798201302441 4142608057534348650976831)
    ·
      refine ⟨6213912086301522976465247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4142608057534348650976831 6213912086301522976465247)
      ·
        refine ⟨9320868129452284464697871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6213912086301522976465247 9320868129452284464697871)
        ·
          refine ⟨13981302194178426697046807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9320868129452284464697871 13981302194178426697046807)
          ·
            refine ⟨20971953291267640045570211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13981302194178426697046807 20971953291267640045570211)
            ·
              refine ⟨31457929936901460068355317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20971953291267640045570211 31457929936901460068355317)
              ·
                refine ⟨2949180931584511881408311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31457929936901460068355317 2949180931584511881408311)
                ·
                  refine ⟨4423771397376767822112467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2949180931584511881408311 4423771397376767822112467)
                  ·
                    refine ⟨6635657096065151733168701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4423771397376767822112467 6635657096065151733168701)
                    ·
                      refine ⟨2488371411024431899938263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6635657096065151733168701 2488371411024431899938263)
                      ·
                        rfl

theorem cell23_4846086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_4846086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846086 prefixEnd_4846086 := by exact prefixLift 4846086
  have htrace : WordTrace (prefixWord ++ tailWord_4846086) baseStart_4846086 baseEnd_4846086 := by
    simpa [prefixWord, tailWord_4846086, baseEnd_4846086] using wordTrace_append hprefix tailTrace_4846086
  have hstable : (prefixWord ++ tailWord_4846086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846086).length < 2 ^ (prefixWord ++ tailWord_4846086).sum := by decide
  have hdescent : baseEnd_4846086 < baseStart_4846086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846092 : List Nat := [2, 2, 1, 2, 4, 1, 1, 5, 1, 2, 2]
def baseStart_4846092 : Nat := 118140960795 + 4846092 * 2 ^ 59
def prefixEnd_4846092 : Nat := 4983230072969 + 3 ^ 40 * 4846092 * 2
def baseEnd_4846092 : Nat := 2488374491908358876463235

theorem tailTrace_4846092 : CollatzResearch.WordTrace tailWord_4846092 prefixEnd_4846092 2488374491908358876463235 := by
  unfold tailWord_4846092
  simp only [CollatzResearch.WordTrace]
  refine ⟨88375747979721902733198265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117834330639629203644264353 88375747979721902733198265)
  ·
    refine ⟨66281810984791427049898699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88375747979721902733198265 66281810984791427049898699)
    ·
      refine ⟨99422716477187140574848049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66281810984791427049898699 99422716477187140574848049)
      ·
        refine ⟨74567037357890355431136037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99422716477187140574848049 74567037357890355431136037)
        ·
          refine ⟨13981319504604441643338007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74567037357890355431136037 13981319504604441643338007)
          ·
            refine ⟨20971979256906662465007011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13981319504604441643338007 20971979256906662465007011)
            ·
              refine ⟨31457968885359993697510517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20971979256906662465007011 31457968885359993697510517)
              ·
                refine ⟨2949184583002499409141611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31457968885359993697510517 2949184583002499409141611)
                ·
                  refine ⟨4423776874503749113712417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2949184583002499409141611 4423776874503749113712417)
                  ·
                    refine ⟨3317832655877811835284313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4423776874503749113712417 3317832655877811835284313)
                    ·
                      refine ⟨2488374491908358876463235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317832655877811835284313 2488374491908358876463235)
                      ·
                        rfl

theorem cell23_4846092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_4846092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846092 prefixEnd_4846092 := by exact prefixLift 4846092
  have htrace : WordTrace (prefixWord ++ tailWord_4846092) baseStart_4846092 baseEnd_4846092 := by
    simpa [prefixWord, tailWord_4846092, baseEnd_4846092] using wordTrace_append hprefix tailTrace_4846092
  have hstable : (prefixWord ++ tailWord_4846092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846092).length < 2 ^ (prefixWord ++ tailWord_4846092).sum := by decide
  have hdescent : baseEnd_4846092 < baseStart_4846092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846119 : List Nat := [1, 1, 7, 2, 1, 1, 3, 1, 2, 4]
def baseStart_4846119 : Nat := 118140960795 + 4846119 * 2 ^ 59
def prefixEnd_4846119 : Nat := 4983230072969 + 3 ^ 40 * 4846119 * 2
def baseEnd_4846119 : Nat := 829462785295343423608537

theorem tailTrace_4846119 : CollatzResearch.WordTrace tailWord_4846119 prefixEnd_4846119 829462785295343423608537 := by
  unfold tailWord_4846119
  simp only [CollatzResearch.WordTrace]
  refine ⟨176752480730345989077629411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117834987153563992718419607 176752480730345989077629411)
  ·
    refine ⟨265128721095518983616444117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176752480730345989077629411 265128721095518983616444117)
    ·
      refine ⟨6213954400676226178510409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 265128721095518983616444117 6213954400676226178510409)
      ·
        refine ⟨4660465800507169633882807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6213954400676226178510409 4660465800507169633882807)
        ·
          refine ⟨6990698700760754450824211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4660465800507169633882807 6990698700760754450824211)
          ·
            refine ⟨10486048051141131676236317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6990698700760754450824211 10486048051141131676236317)
            ·
              refine ⟨3932268019177924378588619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10486048051141131676236317 3932268019177924378588619)
              ·
                refine ⟨5898402028766886567882929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3932268019177924378588619 5898402028766886567882929)
                ·
                  refine ⟨4423801521575164925912197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5898402028766886567882929 4423801521575164925912197)
                  ·
                    refine ⟨829462785295343423608537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4423801521575164925912197 829462785295343423608537)
                    ·
                      rfl

theorem cell23_4846119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_4846119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846119 prefixEnd_4846119 := by exact prefixLift 4846119
  have htrace : WordTrace (prefixWord ++ tailWord_4846119) baseStart_4846119 baseEnd_4846119 := by
    simpa [prefixWord, tailWord_4846119, baseEnd_4846119] using wordTrace_append hprefix tailTrace_4846119
  have hstable : (prefixWord ++ tailWord_4846119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846119).length < 2 ^ (prefixWord ++ tailWord_4846119).sum := by decide
  have hdescent : baseEnd_4846119 < baseStart_4846119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846132 : List Nat := [2, 5, 1, 3, 1, 2, 2, 7]
def baseStart_4846132 : Nat := 118140960795 + 4846132 * 2 ^ 59
def prefixEnd_4846132 : Nat := 4983230072969 + 3 ^ 40 * 4846132 * 2
def baseEnd_4846132 : Nat := 92162778930908841480113

theorem tailTrace_4846132 : CollatzResearch.WordTrace tailWord_4846132 prefixEnd_4846132 92162778930908841480113 := by
  unfold tailWord_4846132
  simp only [CollatzResearch.WordTrace]
  refine ⟨88376477439649446148926325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117835303252865928198568433 88376477439649446148926325)
  ·
    refine ⟨8285294759967135576461843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88376477439649446148926325 8285294759967135576461843)
    ·
      refine ⟨12427942139950703364692765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8285294759967135576461843 12427942139950703364692765)
      ·
        refine ⟨4660478302481513761759787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12427942139950703364692765 4660478302481513761759787)
        ·
          refine ⟨6990717453722270642639681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4660478302481513761759787 6990717453722270642639681)
          ·
            refine ⟨5243038090291702981979761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6990717453722270642639681 5243038090291702981979761)
            ·
              refine ⟨3932278567718777236484821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5243038090291702981979761 3932278567718777236484821)
              ·
                refine ⟨92162778930908841480113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3932278567718777236484821 92162778930908841480113)
                ·
                  rfl

theorem cell23_4846132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 7].length) (baseStart_4846132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846132 prefixEnd_4846132 := by exact prefixLift 4846132
  have htrace : WordTrace (prefixWord ++ tailWord_4846132) baseStart_4846132 baseEnd_4846132 := by
    simpa [prefixWord, tailWord_4846132, baseEnd_4846132] using wordTrace_append hprefix tailTrace_4846132
  have hstable : (prefixWord ++ tailWord_4846132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846132).length < 2 ^ (prefixWord ++ tailWord_4846132).sum := by decide
  have hdescent : baseEnd_4846132 < baseStart_4846132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846135 : List Nat := [1, 1, 3, 1, 2, 3, 4, 2, 1, 3, 2]
def baseStart_4846135 : Nat := 118140960795 + 4846135 * 2 ^ 59
def prefixEnd_4846135 : Nat := 4983230072969 + 3 ^ 40 * 4846135 * 2
def baseEnd_4846135 : Nat := 2488396571576502208225537

theorem tailTrace_4846135 : CollatzResearch.WordTrace tailWord_4846135 prefixEnd_4846135 2488396571576502208225537 := by
  unfold tailWord_4846135
  simp only [CollatzResearch.WordTrace]
  refine ⟨176753064298288023810211859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117835376198858682540141239 176753064298288023810211859)
  ·
    refine ⟨265129596447432035715317789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176753064298288023810211859 265129596447432035715317789)
    ·
      refine ⟨99423598667787013393244171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265129596447432035715317789 99423598667787013393244171)
      ·
        refine ⟨149135398001680520089866257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99423598667787013393244171 149135398001680520089866257)
        ·
          refine ⟨111851548501260390067399693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149135398001680520089866257 111851548501260390067399693)
          ·
            refine ⟨41944330687972646275274885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111851548501260390067399693 41944330687972646275274885)
            ·
              refine ⟨7864562003994871176614041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41944330687972646275274885 7864562003994871176614041)
              ·
                refine ⟨5898421502996153382460531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7864562003994871176614041 5898421502996153382460531)
                ·
                  refine ⟨8847632254494230073690797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5898421502996153382460531 8847632254494230073690797)
                  ·
                    refine ⟨3317862095435336277634049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8847632254494230073690797 3317862095435336277634049)
                    ·
                      refine ⟨2488396571576502208225537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317862095435336277634049 2488396571576502208225537)
                      ·
                        rfl

theorem cell23_4846135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 3, 2].length) (baseStart_4846135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846135 prefixEnd_4846135 := by exact prefixLift 4846135
  have htrace : WordTrace (prefixWord ++ tailWord_4846135) baseStart_4846135 baseEnd_4846135 := by
    simpa [prefixWord, tailWord_4846135, baseEnd_4846135] using wordTrace_append hprefix tailTrace_4846135
  have hstable : (prefixWord ++ tailWord_4846135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846135).length < 2 ^ (prefixWord ++ tailWord_4846135).sum := by decide
  have hdescent : baseEnd_4846135 < baseStart_4846135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846151 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_4846151 : Nat := 118140960795 + 4846151 * 2 ^ 59
def prefixEnd_4846151 : Nat := 4983230072969 + 3 ^ 40 * 4846151 * 2
def baseEnd_4846151 : Nat := 2488404787266974145625463

theorem tailTrace_4846151 : CollatzResearch.WordTrace tailWord_4846151 prefixEnd_4846151 2488404787266974145625463 := by
  unfold tailWord_4846151
  simp only [CollatzResearch.WordTrace]
  refine ⟨176753647866230058542794307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117835765244153372361862871 176753647866230058542794307)
  ·
    refine ⟨265130471799345087814191461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176753647866230058542794307 265130471799345087814191461)
    ·
      refine ⟨49711963462377203965160899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265130471799345087814191461 49711963462377203965160899)
      ·
        refine ⟨74567945193565805947741349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49711963462377203965160899 74567945193565805947741349)
        ·
          refine ⟨13981489723793588615201503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74567945193565805947741349 13981489723793588615201503)
          ·
            refine ⟨20972234585690382922802255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13981489723793588615201503 20972234585690382922802255)
            ·
              refine ⟨31458351878535574384203383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20972234585690382922802255 31458351878535574384203383)
              ·
                refine ⟨47187527817803361576305075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31458351878535574384203383 47187527817803361576305075)
                ·
                  refine ⟨70781291726705042364457613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47187527817803361576305075 70781291726705042364457613)
                  ·
                    refine ⟨26542984397514390886671605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70781291726705042364457613 26542984397514390886671605)
                    ·
                      refine ⟨2488404787266974145625463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26542984397514390886671605 2488404787266974145625463)
                      ·
                        rfl

theorem cell23_4846151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_4846151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846151 prefixEnd_4846151 := by exact prefixLift 4846151
  have htrace : WordTrace (prefixWord ++ tailWord_4846151) baseStart_4846151 baseEnd_4846151 := by
    simpa [prefixWord, tailWord_4846151, baseEnd_4846151] using wordTrace_append hprefix tailTrace_4846151
  have hstable : (prefixWord ++ tailWord_4846151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846151).length < 2 ^ (prefixWord ++ tailWord_4846151).sum := by decide
  have hdescent : baseEnd_4846151 < baseStart_4846151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846165 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 4, 2, 2]
def baseStart_4846165 : Nat := 118140960795 + 4846165 * 2 ^ 59
def prefixEnd_4846165 : Nat := 4983230072969 + 3 ^ 40 * 4846165 * 2
def baseEnd_4846165 : Nat := 2488411975996137090850399

theorem tailTrace_4846165 : CollatzResearch.WordTrace tailWord_4846165 prefixEnd_4846165 2488411975996137090850399 := by
  unfold tailWord_4846165
  simp only [CollatzResearch.WordTrace]
  refine ⟨176754158488179338933803949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117836105658786225955869299 176754158488179338933803949)
  ·
    refine ⟨66282809433067252100176481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176754158488179338933803949 66282809433067252100176481)
    ·
      refine ⟨49712107074800439075132361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66282809433067252100176481 49712107074800439075132361)
      ·
        refine ⟨37284080306100329306349271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49712107074800439075132361 37284080306100329306349271)
        ·
          refine ⟨55926120459150493959523907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37284080306100329306349271 55926120459150493959523907)
          ·
            refine ⟨83889180688725740939285861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55926120459150493959523907 83889180688725740939285861)
            ·
              refine ⟨15729221379136076426116099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83889180688725740939285861 15729221379136076426116099)
              ·
                refine ⟨23593832068704114639174149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15729221379136076426116099 23593832068704114639174149)
                ·
                  refine ⟨4423843512882021494845153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23593832068704114639174149 4423843512882021494845153)
                  ·
                    refine ⟨3317882634661516121133865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4423843512882021494845153 3317882634661516121133865)
                    ·
                      refine ⟨2488411975996137090850399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317882634661516121133865 2488411975996137090850399)
                      ·
                        rfl

theorem cell23_4846165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_4846165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846165 prefixEnd_4846165 := by exact prefixLift 4846165
  have htrace : WordTrace (prefixWord ++ tailWord_4846165) baseStart_4846165 baseEnd_4846165 := by
    simpa [prefixWord, tailWord_4846165, baseEnd_4846165] using wordTrace_append hprefix tailTrace_4846165
  have hstable : (prefixWord ++ tailWord_4846165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846165).length < 2 ^ (prefixWord ++ tailWord_4846165).sum := by decide
  have hdescent : baseEnd_4846165 < baseStart_4846165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846211 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 5]
def baseStart_4846211 : Nat := 118140960795 + 4846211 * 2 ^ 59
def prefixEnd_4846211 : Nat := 4983230072969 + 3 ^ 40 * 4846211 * 2
def baseEnd_4846211 : Nat := 2488435596106243910875187

theorem tailTrace_4846211 : CollatzResearch.WordTrace tailWord_4846211 prefixEnd_4846211 2488435596106243910875187 := by
  unfold tailWord_4846211
  simp only [CollatzResearch.WordTrace]
  refine ⟨176755836246012688789978487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117837224164008459193318991 176755836246012688789978487)
  ·
    refine ⟨265133754369019033184967731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176755836246012688789978487 265133754369019033184967731)
    ·
      refine ⟨397700631553528549777451597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265133754369019033184967731 397700631553528549777451597)
      ·
        refine ⟨149137736832573206166544349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 397700631553528549777451597 149137736832573206166544349)
        ·
          refine ⟨55926651312214952312454131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149137736832573206166544349 55926651312214952312454131)
          ·
            refine ⟨83889976968322428468681197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55926651312214952312454131 83889976968322428468681197)
            ·
              refine ⟨31458741363120910675755449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83889976968322428468681197 31458741363120910675755449)
              ·
                refine ⟨23594056022340683006816587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31458741363120910675755449 23594056022340683006816587)
                ·
                  refine ⟨35391084033511024510224881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23594056022340683006816587 35391084033511024510224881)
                  ·
                    refine ⟨26543313025133268382668661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35391084033511024510224881 26543313025133268382668661)
                    ·
                      refine ⟨2488435596106243910875187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26543313025133268382668661 2488435596106243910875187)
                      ·
                        rfl

theorem cell23_4846211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_4846211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846211 prefixEnd_4846211 := by exact prefixLift 4846211
  have htrace : WordTrace (prefixWord ++ tailWord_4846211) baseStart_4846211 baseEnd_4846211 := by
    simpa [prefixWord, tailWord_4846211, baseEnd_4846211] using wordTrace_append hprefix tailTrace_4846211
  have hstable : (prefixWord ++ tailWord_4846211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846211).length < 2 ^ (prefixWord ++ tailWord_4846211).sum := by decide
  have hdescent : baseEnd_4846211 < baseStart_4846211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846255 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 2, 1, 4]
def baseStart_4846255 : Nat := 118140960795 + 4846255 * 2 ^ 59
def prefixEnd_4846255 : Nat := 4983230072969 + 3 ^ 40 * 4846255 * 2
def baseEnd_4846255 : Nat := 2488458189255041738724985

theorem tailTrace_4846255 : CollatzResearch.WordTrace tailWord_4846255 prefixEnd_4846255 2488458189255041738724985 := by
  unfold tailWord_4846255
  simp only [CollatzResearch.WordTrace]
  refine ⟨176757441057853284304580219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117838294038568856203053479 176757441057853284304580219)
  ·
    refine ⟨265136161586779926456870329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176757441057853284304580219 265136161586779926456870329)
    ·
      refine ⟨198852121190084944842652747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265136161586779926456870329 198852121190084944842652747)
      ·
        refine ⟨298278181785127417263979121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198852121190084944842652747 298278181785127417263979121)
        ·
          refine ⟨223708636338845562947984341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298278181785127417263979121 223708636338845562947984341)
          ·
            refine ⟨5243171164191692881593383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 223708636338845562947984341 5243171164191692881593383)
            ·
              refine ⟨7864756746287539322390075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5243171164191692881593383 7864756746287539322390075)
              ·
                refine ⟨11797135119431308983585113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7864756746287539322390075 11797135119431308983585113)
                ·
                  refine ⟨8847851339573481737688835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11797135119431308983585113 8847851339573481737688835)
                  ·
                    refine ⟨13271777009360222606533253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8847851339573481737688835 13271777009360222606533253)
                    ·
                      refine ⟨2488458189255041738724985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13271777009360222606533253 2488458189255041738724985)
                      ·
                        rfl

theorem cell23_4846255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 1, 4].length) (baseStart_4846255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846255 prefixEnd_4846255 := by exact prefixLift 4846255
  have htrace : WordTrace (prefixWord ++ tailWord_4846255) baseStart_4846255 baseEnd_4846255 := by
    simpa [prefixWord, tailWord_4846255, baseEnd_4846255] using wordTrace_append hprefix tailTrace_4846255
  have hstable : (prefixWord ++ tailWord_4846255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846255).length < 2 ^ (prefixWord ++ tailWord_4846255).sum := by decide
  have hdescent : baseEnd_4846255 < baseStart_4846255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846282 : List Nat := [3, 1, 2, 1, 4, 1, 2, 4, 1, 4]
def baseStart_4846282 : Nat := 118140960795 + 4846282 * 2 ^ 59
def prefixEnd_4846282 : Nat := 4983230072969 + 3 ^ 40 * 4846282 * 2
def baseEnd_4846282 : Nat := 829490684410904377695787

theorem tailTrace_4846282 : CollatzResearch.WordTrace tailWord_4846282 prefixEnd_4846282 829490684410904377695787 := by
  unfold tailWord_4846282
  simp only [CollatzResearch.WordTrace]
  refine ⟨44189606457188866978953275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117838950552503645277208733 44189606457188866978953275)
  ·
    refine ⟨66284409685783300468429913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44189606457188866978953275 66284409685783300468429913)
    ·
      refine ⟨49713307264337475351322435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66284409685783300468429913 49713307264337475351322435)
      ·
        refine ⟨74569960896506213026983653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49713307264337475351322435 74569960896506213026983653)
        ·
          refine ⟨13981867668094914942559435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74569960896506213026983653 13981867668094914942559435)
          ·
            refine ⟨20972801502142372413839153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13981867668094914942559435 20972801502142372413839153)
            ·
              refine ⟨15729601126606779310379365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20972801502142372413839153 15729601126606779310379365)
              ·
                refine ⟨2949300211238771120696131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15729601126606779310379365 2949300211238771120696131)
                ·
                  refine ⟨4423950316858156681044197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2949300211238771120696131 4423950316858156681044197)
                  ·
                    refine ⟨829490684410904377695787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4423950316858156681044197 829490684410904377695787)
                    ·
                      rfl

theorem cell23_4846282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_4846282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846282 prefixEnd_4846282 := by exact prefixLift 4846282
  have htrace : WordTrace (prefixWord ++ tailWord_4846282) baseStart_4846282 baseEnd_4846282 := by
    simpa [prefixWord, tailWord_4846282, baseEnd_4846282] using wordTrace_append hprefix tailTrace_4846282
  have hstable : (prefixWord ++ tailWord_4846282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846282).length < 2 ^ (prefixWord ++ tailWord_4846282).sum := by decide
  have hdescent : baseEnd_4846282 < baseStart_4846282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846295 : List Nat := [1, 1, 3, 2, 1, 5, 3, 1, 6]
def baseStart_4846295 : Nat := 118140960795 + 4846295 * 2 ^ 59
def prefixEnd_4846295 : Nat := 4983230072969 + 3 ^ 40 * 4846295 * 2
def baseEnd_4846295 : Nat := 276497636497913509136089

theorem tailTrace_4846295 : CollatzResearch.WordTrace tailWord_4846295 prefixEnd_4846295 276497636497913509136089 := by
  unfold tailWord_4846295
  simp only [CollatzResearch.WordTrace]
  refine ⟨176758899977708371136036339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117839266651805580757357559 176758899977708371136036339)
  ·
    refine ⟨265138349966562556704054509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176758899977708371136036339 265138349966562556704054509)
    ·
      refine ⟨99426881237460958764020441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265138349966562556704054509 99426881237460958764020441)
      ·
        refine ⟨74570160928095719073015331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99426881237460958764020441 74570160928095719073015331)
        ·
          refine ⟨111855241392143578609522997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74570160928095719073015331 111855241392143578609522997)
          ·
            refine ⟨10486428880513460494642781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111855241392143578609522997 10486428880513460494642781)
            ·
              refine ⟨3932410830192547685491043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10486428880513460494642781 3932410830192547685491043)
              ·
                refine ⟨5898616245288821528236565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3932410830192547685491043 5898616245288821528236565)
                ·
                  refine ⟨276497636497913509136089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5898616245288821528236565 276497636497913509136089)
                  ·
                    rfl

theorem cell23_4846295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 6].length) (baseStart_4846295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846295 prefixEnd_4846295 := by exact prefixLift 4846295
  have htrace : WordTrace (prefixWord ++ tailWord_4846295) baseStart_4846295 baseEnd_4846295 := by
    simpa [prefixWord, tailWord_4846295, baseEnd_4846295] using wordTrace_append hprefix tailTrace_4846295
  have hstable : (prefixWord ++ tailWord_4846295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846295).length < 2 ^ (prefixWord ++ tailWord_4846295).sum := by decide
  have hdescent : baseEnd_4846295 < baseStart_4846295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846315 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 2, 3, 2]
def baseStart_4846315 : Nat := 118140960795 + 4846315 * 2 ^ 59
def prefixEnd_4846315 : Nat := 4983230072969 + 3 ^ 40 * 4846315 * 2
def baseEnd_4846315 : Nat := 2488488998094311503974709

theorem tailTrace_4846315 : CollatzResearch.WordTrace tailWord_4846315 prefixEnd_4846315 2488488998094311503974709 := by
  unfold tailWord_4846315
  simp only [CollatzResearch.WordTrace]
  refine ⟨176759629437635914551764399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117839752958423943034509599 176759629437635914551764399)
  ·
    refine ⟨265139444156453871827646599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176759629437635914551764399 265139444156453871827646599)
    ·
      refine ⟨397709166234680807741469899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265139444156453871827646599 397709166234680807741469899)
      ·
        refine ⟨596563749352021211612204849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397709166234680807741469899 596563749352021211612204849)
        ·
          refine ⟨447422812014015908709153637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 596563749352021211612204849 447422812014015908709153637)
          ·
            refine ⟨83891777252627982882966307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 447422812014015908709153637 83891777252627982882966307)
            ·
              refine ⟨125837665878941974324449461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83891777252627982882966307 125837665878941974324449461)
              ·
                refine ⟨11797281176150810092917137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125837665878941974324449461 11797281176150810092917137)
                ·
                  refine ⟨8847960882113107569687853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11797281176150810092917137 8847960882113107569687853)
                  ·
                    refine ⟨3317985330792415338632945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8847960882113107569687853 3317985330792415338632945)
                    ·
                      refine ⟨2488488998094311503974709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317985330792415338632945 2488488998094311503974709)
                      ·
                        rfl

theorem cell23_4846315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 3, 2].length) (baseStart_4846315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846315 prefixEnd_4846315 := by exact prefixLift 4846315
  have htrace : WordTrace (prefixWord ++ tailWord_4846315) baseStart_4846315 baseEnd_4846315 := by
    simpa [prefixWord, tailWord_4846315, baseEnd_4846315] using wordTrace_append hprefix tailTrace_4846315
  have hstable : (prefixWord ++ tailWord_4846315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846315).length < 2 ^ (prefixWord ++ tailWord_4846315).sum := by decide
  have hdescent : baseEnd_4846315 < baseStart_4846315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846332 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 2, 3, 2]
def baseStart_4846332 : Nat := 118140960795 + 4846332 * 2 ^ 59
def prefixEnd_4846332 : Nat := 4983230072969 + 3 ^ 40 * 4846332 * 2
def baseEnd_4846332 : Nat := 2488497727265437937462131

theorem tailTrace_4846332 : CollatzResearch.WordTrace tailWord_4846332 prefixEnd_4846332 2488497727265437937462131 := by
  unfold tailWord_4846332
  simp only [CollatzResearch.WordTrace]
  refine ⟨88380124739287163227566625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117840166319049550970088833 88380124739287163227566625)
  ·
    refine ⟨66285093554465372420674969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88380124739287163227566625 66285093554465372420674969)
    ·
      refine ⟨49713820165849029315506227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66285093554465372420674969 49713820165849029315506227)
      ·
        refine ⟨74570730248773543973259341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49713820165849029315506227 74570730248773543973259341)
        ·
          refine ⟨27964023843290078989972253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74570730248773543973259341 27964023843290078989972253)
          ·
            refine ⟨10486508941233779621239595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27964023843290078989972253 10486508941233779621239595)
            ·
              refine ⟨15729763411850669431859393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10486508941233779621239595 15729763411850669431859393)
              ·
                refine ⟨11797322558888002073894545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15729763411850669431859393 11797322558888002073894545)
                ·
                  refine ⟨8847991919166001555420909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11797322558888002073894545 8847991919166001555420909)
                  ·
                    refine ⟨3317996969687250583282841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8847991919166001555420909 3317996969687250583282841)
                    ·
                      refine ⟨2488497727265437937462131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317996969687250583282841 2488497727265437937462131)
                      ·
                        rfl

theorem cell23_4846332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_4846332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846332 prefixEnd_4846332 := by exact prefixLift 4846332
  have htrace : WordTrace (prefixWord ++ tailWord_4846332) baseStart_4846332 baseEnd_4846332 := by
    simpa [prefixWord, tailWord_4846332, baseEnd_4846332] using wordTrace_append hprefix tailTrace_4846332
  have hstable : (prefixWord ++ tailWord_4846332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846332).length < 2 ^ (prefixWord ++ tailWord_4846332).sum := by decide
  have hdescent : baseEnd_4846332 < baseStart_4846332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846348 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 2, 6, 3]
def baseStart_4846348 : Nat := 118140960795 + 4846348 * 2 ^ 59
def prefixEnd_4846348 : Nat := 4983230072969 + 3 ^ 40 * 4846348 * 2
def baseEnd_4846348 : Nat := 2488505942955909874862057

theorem tailTrace_4846348 : CollatzResearch.WordTrace tailWord_4846348 prefixEnd_4846348 2488505942955909874862057 := by
  unfold tailWord_4846348
  simp only [CollatzResearch.WordTrace]
  refine ⟨88380416523258180593857849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117840555364344240791810465 88380416523258180593857849)
  ·
    refine ⟨66285312392443635445393387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88380416523258180593857849 66285312392443635445393387)
    ·
      refine ⟨99427968588665453168090081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66285312392443635445393387 99427968588665453168090081)
      ·
        refine ⟨74570976441499089876067561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99427968588665453168090081 74570976441499089876067561)
        ·
          refine ⟨55928232331124317407050671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74570976441499089876067561 55928232331124317407050671)
          ·
            refine ⟨83892348496686476110576007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55928232331124317407050671 83892348496686476110576007)
            ·
              refine ⟨125838522745029714165864011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83892348496686476110576007 125838522745029714165864011)
              ·
                refine ⟨188757784117544571248796017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125838522745029714165864011 188757784117544571248796017)
                ·
                  refine ⟨141568338088158428436597013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188757784117544571248796017 141568338088158428436597013)
                  ·
                    refine ⟨6636015847882426332965485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 141568338088158428436597013 6636015847882426332965485)
                    ·
                      refine ⟨2488505942955909874862057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6636015847882426332965485 2488505942955909874862057)
                      ·
                        rfl

theorem cell23_4846348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_4846348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846348 prefixEnd_4846348 := by exact prefixLift 4846348
  have htrace : WordTrace (prefixWord ++ tailWord_4846348) baseStart_4846348 baseEnd_4846348 := by
    simpa [prefixWord, tailWord_4846348, baseEnd_4846348] using wordTrace_append hprefix tailTrace_4846348
  have hstable : (prefixWord ++ tailWord_4846348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846348).length < 2 ^ (prefixWord ++ tailWord_4846348).sum := by decide
  have hdescent : baseEnd_4846348 < baseStart_4846348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846355 : List Nat := [1, 1, 1, 2, 1, 3, 5, 3, 2, 4]
def baseStart_4846355 : Nat := 118140960795 + 4846355 * 2 ^ 59
def prefixEnd_4846355 : Nat := 4983230072969 + 3 ^ 40 * 4846355 * 2
def baseEnd_4846355 : Nat := 829503179106830449158175

theorem tailTrace_4846355 : CollatzResearch.WordTrace tailWord_4846355 prefixEnd_4846355 829503179106830449158175 := by
  unfold tailWord_4846355
  simp only [CollatzResearch.WordTrace]
  refine ⟨176761088357491001383220519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117840725571660667588813679 176761088357491001383220519)
  ·
    refine ⟨265141632536236502074830779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176761088357491001383220519 265141632536236502074830779)
    ·
      refine ⟨397712448804354753112246169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265141632536236502074830779 397712448804354753112246169)
      ·
        refine ⟨298284336603266064834184627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397712448804354753112246169 298284336603266064834184627)
        ·
          refine ⟨447426504904899097251276941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298284336603266064834184627 447426504904899097251276941)
          ·
            refine ⟨167784939339337161469228853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 447426504904899097251276941 167784939339337161469228853)
            ·
              refine ⟨15729838063062858887740205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167784939339337161469228853 15729838063062858887740205)
              ·
                refine ⟨5898689273648572082902577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15729838063062858887740205 5898689273648572082902577)
                ·
                  refine ⟨4424016955236429062176933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5898689273648572082902577 4424016955236429062176933)
                  ·
                    refine ⟨829503179106830449158175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4424016955236429062176933 829503179106830449158175)
                    ·
                      rfl

theorem cell23_4846355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 4].length) (baseStart_4846355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846355 prefixEnd_4846355 := by exact prefixLift 4846355
  have htrace : WordTrace (prefixWord ++ tailWord_4846355) baseStart_4846355 baseEnd_4846355 := by
    simpa [prefixWord, tailWord_4846355, baseEnd_4846355] using wordTrace_append hprefix tailTrace_4846355
  have hstable : (prefixWord ++ tailWord_4846355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846355).length < 2 ^ (prefixWord ++ tailWord_4846355).sum := by decide
  have hdescent : baseEnd_4846355 < baseStart_4846355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846359 : List Nat := [1, 1, 3, 4, 4, 1, 1, 2, 1, 5]
def baseStart_4846359 : Nat := 118140960795 + 4846359 * 2 ^ 59
def prefixEnd_4846359 : Nat := 4983230072969 + 3 ^ 40 * 4846359 * 2
def baseEnd_4846359 : Nat := 829503863747703110608169

theorem tailTrace_4846359 : CollatzResearch.WordTrace tailWord_4846359 prefixEnd_4846359 829503863747703110608169 := by
  unfold tailWord_4846359
  simp only [CollatzResearch.WordTrace]
  refine ⟨176761234249476510066366131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117840822832984340044244087 176761234249476510066366131)
  ·
    refine ⟨265141851374214765099549197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176761234249476510066366131 265141851374214765099549197)
    ·
      refine ⟨99428194265330536912330949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265141851374214765099549197 99428194265330536912330949)
      ·
        refine ⟨18642786424749475671062053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99428194265330536912330949 18642786424749475671062053)
        ·
          refine ⟨3495522454640526688324135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18642786424749475671062053 3495522454640526688324135)
          ·
            refine ⟨5243283681960790032486203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3495522454640526688324135 5243283681960790032486203)
            ·
              refine ⟨7864925522941185048729305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5243283681960790032486203 7864925522941185048729305)
              ·
                refine ⟨5898694142205888786546979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7864925522941185048729305 5898694142205888786546979)
                ·
                  refine ⟨8848041213308833179820469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5898694142205888786546979 8848041213308833179820469)
                  ·
                    refine ⟨829503863747703110608169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8848041213308833179820469 829503863747703110608169)
                    ·
                      rfl

theorem cell23_4846359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 1, 5].length) (baseStart_4846359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846359 prefixEnd_4846359 := by exact prefixLift 4846359
  have htrace : WordTrace (prefixWord ++ tailWord_4846359) baseStart_4846359 baseEnd_4846359 := by
    simpa [prefixWord, tailWord_4846359, baseEnd_4846359] using wordTrace_append hprefix tailTrace_4846359
  have hstable : (prefixWord ++ tailWord_4846359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846359).length < 2 ^ (prefixWord ++ tailWord_4846359).sum := by decide
  have hdescent : baseEnd_4846359 < baseStart_4846359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846362 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2]
def baseStart_4846362 : Nat := 118140960795 + 4846362 * 2 ^ 59
def prefixEnd_4846362 : Nat := 4983230072969 + 3 ^ 40 * 4846362 * 2
def baseEnd_4846362 : Nat := 2488513131685072820086993

theorem tailTrace_4846362 : CollatzResearch.WordTrace tailWord_4846362 prefixEnd_4846362 2488513131685072820086993 := by
  unfold tailWord_4846362
  simp only [CollatzResearch.WordTrace]
  refine ⟨44190335917116410394681335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117840895778977094385816893 44190335917116410394681335)
  ·
    refine ⟨66285503875674615592022003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44190335917116410394681335 66285503875674615592022003)
    ·
      refine ⟨99428255813511923388033005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66285503875674615592022003 99428255813511923388033005)
      ·
        refine ⟨37285595930066971270512377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99428255813511923388033005 37285595930066971270512377)
        ·
          refine ⟨27964196947550228452884283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37285595930066971270512377 27964196947550228452884283)
          ·
            refine ⟨41946295421325342679326425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27964196947550228452884283 41946295421325342679326425)
            ·
              refine ⟨31459721565994007009494819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41946295421325342679326425 31459721565994007009494819)
              ·
                refine ⟨47189582348991010514242229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31459721565994007009494819 47189582348991010514242229)
                ·
                  refine ⟨4424023345217907235710209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47189582348991010514242229 4424023345217907235710209)
                  ·
                    refine ⟨3318017508913430426782657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4424023345217907235710209 3318017508913430426782657)
                    ·
                      refine ⟨2488513131685072820086993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3318017508913430426782657 2488513131685072820086993)
                      ·
                        rfl

theorem cell23_4846362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_4846362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846362 prefixEnd_4846362 := by exact prefixLift 4846362
  have htrace : WordTrace (prefixWord ++ tailWord_4846362) baseStart_4846362 baseEnd_4846362 := by
    simpa [prefixWord, tailWord_4846362, baseEnd_4846362] using wordTrace_append hprefix tailTrace_4846362
  have hstable : (prefixWord ++ tailWord_4846362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846362).length < 2 ^ (prefixWord ++ tailWord_4846362).sum := by decide
  have hdescent : baseEnd_4846362 < baseStart_4846362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846368 : List Nat := [2, 1, 1, 5, 1, 2, 2, 9]
def baseStart_4846368 : Nat := 118140960795 + 4846368 * 2 ^ 59
def prefixEnd_4846368 : Nat := 4983230072969 + 3 ^ 40 * 4846368 * 2
def baseEnd_4846368 : Nat := 92167267132185177652295

theorem tailTrace_4846368 : CollatzResearch.WordTrace tailWord_4846368 prefixEnd_4846368 92167267132185177652295 := by
  unfold tailWord_4846368
  simp only [CollatzResearch.WordTrace]
  refine ⟨88380781253221952301721879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117841041670962603068962505 88380781253221952301721879)
  ·
    refine ⟨132571171879832928452582819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88380781253221952301721879 132571171879832928452582819)
    ·
      refine ⟨198856757819749392678874229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132571171879832928452582819 198856757819749392678874229)
      ·
        refine ⟨18642821045601505563644459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 198856757819749392678874229 18642821045601505563644459)
        ·
          refine ⟨27964231568402258345466689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18642821045601505563644459 27964231568402258345466689)
          ·
            refine ⟨20973173676301693759100017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27964231568402258345466689 20973173676301693759100017)
            ·
              refine ⟨15729880257226270319325013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20973173676301693759100017 15729880257226270319325013)
              ·
                refine ⟨92167267132185177652295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15729880257226270319325013 92167267132185177652295)
                ·
                  rfl

theorem cell23_4846368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 9].length) (baseStart_4846368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846368 prefixEnd_4846368 := by exact prefixLift 4846368
  have htrace : WordTrace (prefixWord ++ tailWord_4846368) baseStart_4846368 baseEnd_4846368 := by
    simpa [prefixWord, tailWord_4846368, baseEnd_4846368] using wordTrace_append hprefix tailTrace_4846368
  have hstable : (prefixWord ++ tailWord_4846368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846368).length < 2 ^ (prefixWord ++ tailWord_4846368).sum := by decide
  have hdescent : baseEnd_4846368 < baseStart_4846368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846382 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_4846382 : Nat := 118140960795 + 4846382 * 2 ^ 59
def prefixEnd_4846382 : Nat := 4983230072969 + 3 ^ 40 * 4846382 * 2
def baseEnd_4846382 : Nat := 2488523401298162741836901

theorem tailTrace_4846382 : CollatzResearch.WordTrace tailWord_4846382 prefixEnd_4846382 2488523401298162741836901 := by
  unfold tailWord_4846382
  simp only [CollatzResearch.WordTrace]
  refine ⟨22095259141049148124306675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117841382085595456662968933 22095259141049148124306675)
  ·
    refine ⟨33142888711573722186460013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22095259141049148124306675 33142888711573722186460013)
    ·
      refine ⟨12428583266840145819922505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33142888711573722186460013 12428583266840145819922505)
      ·
        refine ⟨9321437450130109364941879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12428583266840145819922505 9321437450130109364941879)
        ·
          refine ⟨13982156175195164047412819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9321437450130109364941879 13982156175195164047412819)
          ·
            refine ⟨20973234262792746071119229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13982156175195164047412819 20973234262792746071119229)
            ·
              refine ⟨7864962848547279776669711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20973234262792746071119229 7864962848547279776669711)
              ·
                refine ⟨11797444272820919665004567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7864962848547279776669711 11797444272820919665004567)
                ·
                  refine ⟨17696166409231379497506851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11797444272820919665004567 17696166409231379497506851)
                  ·
                    refine ⟨26544249613847069246260277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17696166409231379497506851 26544249613847069246260277)
                    ·
                      refine ⟨2488523401298162741836901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26544249613847069246260277 2488523401298162741836901)
                      ·
                        rfl

theorem cell23_4846382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_4846382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846382 prefixEnd_4846382 := by exact prefixLift 4846382
  have htrace : WordTrace (prefixWord ++ tailWord_4846382) baseStart_4846382 baseEnd_4846382 := by
    simpa [prefixWord, tailWord_4846382, baseEnd_4846382] using wordTrace_append hprefix tailTrace_4846382
  have hstable : (prefixWord ++ tailWord_4846382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846382).length < 2 ^ (prefixWord ++ tailWord_4846382).sum := by decide
  have hdescent : baseEnd_4846382 < baseStart_4846382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846390 : List Nat := [5, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3]
def baseStart_4846390 : Nat := 118140960795 + 4846390 * 2 ^ 59
def prefixEnd_4846390 : Nat := 4983230072969 + 3 ^ 40 * 4846390 * 2
def baseEnd_4846390 : Nat := 2488527509143398710536865

theorem tailTrace_4846390 : CollatzResearch.WordTrace tailWord_4846390 prefixEnd_4846390 2488527509143398710536865 := by
  unfold tailWord_4846390
  simp only [CollatzResearch.WordTrace]
  refine ⟨11047647807022762647546539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117841576608242801573829749 11047647807022762647546539)
  ·
    refine ⟨16571471710534143971319809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11047647807022762647546539 16571471710534143971319809)
    ·
      refine ⟨12428603782900607978489857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16571471710534143971319809 12428603782900607978489857)
      ·
        refine ⟨9321452837175455983867393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12428603782900607978489857 9321452837175455983867393)
        ·
          refine ⟨6991089627881591987900545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9321452837175455983867393 6991089627881591987900545)
          ·
            refine ⟨5243317220911193990925409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6991089627881591987900545 5243317220911193990925409)
            ·
              refine ⟨3932487915683395493194057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5243317220911193990925409 3932487915683395493194057)
              ·
                refine ⟨2949365936762546619895543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3932487915683395493194057 2949365936762546619895543)
                ·
                  refine ⟨4424048905143819929843315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2949365936762546619895543 4424048905143819929843315)
                  ·
                    refine ⟨6636073357715729894764973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4424048905143819929843315 6636073357715729894764973)
                    ·
                      refine ⟨2488527509143398710536865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6636073357715729894764973 2488527509143398710536865)
                      ·
                        rfl

theorem cell23_4846390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_4846390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846390 prefixEnd_4846390 := by exact prefixLift 4846390
  have htrace : WordTrace (prefixWord ++ tailWord_4846390) baseStart_4846390 baseEnd_4846390 := by
    simpa [prefixWord, tailWord_4846390, baseEnd_4846390] using wordTrace_append hprefix tailTrace_4846390
  have hstable : (prefixWord ++ tailWord_4846390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846390).length < 2 ^ (prefixWord ++ tailWord_4846390).sum := by decide
  have hdescent : baseEnd_4846390 < baseStart_4846390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846412 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 1, 3, 3]
def baseStart_4846412 : Nat := 118140960795 + 4846412 * 2 ^ 59
def prefixEnd_4846412 : Nat := 4983230072969 + 3 ^ 40 * 4846412 * 2
def baseEnd_4846412 : Nat := 2488538805717797624461763

theorem tailTrace_4846412 : CollatzResearch.WordTrace tailWord_4846412 prefixEnd_4846412 2488538805717797624461763 := by
  unfold tailWord_4846412
  simp only [CollatzResearch.WordTrace]
  refine ⟨88381583659142250059022745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117842111545523000078696993 88381583659142250059022745)
  ·
    refine ⟨66286187744356687544267059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88381583659142250059022745 66286187744356687544267059)
    ·
      refine ⟨99429281616535031316400589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66286187744356687544267059 99429281616535031316400589)
      ·
        refine ⟨37285980606200636743650221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99429281616535031316400589 37285980606200636743650221)
        ·
          refine ⟨13982242727325238778868833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37285980606200636743650221 13982242727325238778868833)
          ·
            refine ⟨10486682045493929084151625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13982242727325238778868833 10486682045493929084151625)
            ·
              refine ⟨7865011534120446813113719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10486682045493929084151625 7865011534120446813113719)
              ·
                refine ⟨11797517301180670219670579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7865011534120446813113719 11797517301180670219670579)
                ·
                  refine ⟨17696275951771005329505869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11797517301180670219670579 17696275951771005329505869)
                  ·
                    refine ⟨6636103481914126998564701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17696275951771005329505869 6636103481914126998564701)
                    ·
                      refine ⟨2488538805717797624461763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6636103481914126998564701 2488538805717797624461763)
                      ·
                        rfl

theorem cell23_4846412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_4846412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846412 prefixEnd_4846412 := by exact prefixLift 4846412
  have htrace : WordTrace (prefixWord ++ tailWord_4846412) baseStart_4846412 baseEnd_4846412 := by
    simpa [prefixWord, tailWord_4846412, baseEnd_4846412] using wordTrace_append hprefix tailTrace_4846412
  have hstable : (prefixWord ++ tailWord_4846412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846412).length < 2 ^ (prefixWord ++ tailWord_4846412).sum := by decide
  have hdescent : baseEnd_4846412 < baseStart_4846412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846439 : List Nat := [1, 1, 5, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_4846439 : Nat := 118140960795 + 4846439 * 2 ^ 59
def prefixEnd_4846439 : Nat := 4983230072969 + 3 ^ 40 * 4846439 * 2
def baseEnd_4846439 : Nat := 2488552669695469018824139

theorem tailTrace_4846439 : CollatzResearch.WordTrace tailWord_4846439 prefixEnd_4846439 2488552669695469018824139 := by
  unfold tailWord_4846439
  simp only [CollatzResearch.WordTrace]
  refine ⟨176764152089186683729278371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117842768059457789152852247 176764152089186683729278371)
  ·
    refine ⟨265146228133780025593917557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176764152089186683729278371 265146228133780025593917557)
    ·
      refine ⟨24857458887541877399429771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 265146228133780025593917557 24857458887541877399429771)
      ·
        refine ⟨37286188331312816099144657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24857458887541877399429771 37286188331312816099144657)
        ·
          refine ⟨27964641248484612074358493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37286188331312816099144657 27964641248484612074358493)
          ·
            refine ⟨10486740468181729527884435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27964641248484612074358493 10486740468181729527884435)
            ·
              refine ⟨15730110702272594291826653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10486740468181729527884435 15730110702272594291826653)
              ·
                refine ⟨5898791513352222859434995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15730110702272594291826653 5898791513352222859434995)
                ·
                  refine ⟨8848187270028334289152493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5898791513352222859434995 8848187270028334289152493)
                  ·
                    refine ⟨3318070226260625358432185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8848187270028334289152493 3318070226260625358432185)
                    ·
                      refine ⟨2488552669695469018824139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3318070226260625358432185 2488552669695469018824139)
                      ·
                        rfl

theorem cell23_4846439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_4846439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846439 prefixEnd_4846439 := by exact prefixLift 4846439
  have htrace : WordTrace (prefixWord ++ tailWord_4846439) baseStart_4846439 baseEnd_4846439 := by
    simpa [prefixWord, tailWord_4846439, baseEnd_4846439] using wordTrace_append hprefix tailTrace_4846439
  have hstable : (prefixWord ++ tailWord_4846439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846439).length < 2 ^ (prefixWord ++ tailWord_4846439).sum := by decide
  have hdescent : baseEnd_4846439 < baseStart_4846439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846469 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 1, 4, 2]
def baseStart_4846469 : Nat := 118140960795 + 4846469 * 2 ^ 59
def prefixEnd_4846469 : Nat := 4983230072969 + 3 ^ 40 * 4846469 * 2
def baseEnd_4846469 : Nat := 2488568074115103901449001

theorem tailTrace_4846469 : CollatzResearch.WordTrace tailWord_4846469 prefixEnd_4846469 2488568074115103901449001 := by
  unfold tailWord_4846469
  simp only [CollatzResearch.WordTrace]
  refine ⟨176765246279077998852870461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117843497519385332568580307 176765246279077998852870461)
  ·
    refine ⟨66286967354654249569826423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176765246279077998852870461 66286967354654249569826423)
    ·
      refine ⟨99430451031981374354739635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66286967354654249569826423 99430451031981374354739635)
      ·
        refine ⟨149145676547972061532109453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99430451031981374354739635 149145676547972061532109453)
        ·
          refine ⟨55929628705489523074541045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149145676547972061532109453 55929628705489523074541045)
          ·
            refine ⟨5243402691139642788238223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55929628705489523074541045 5243402691139642788238223)
            ·
              refine ⟨7865104036709464182357335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5243402691139642788238223 7865104036709464182357335)
              ·
                refine ⟨11797656055064196273536003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7865104036709464182357335 11797656055064196273536003)
                ·
                  refine ⟨17696484082596294410304005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11797656055064196273536003 17696484082596294410304005)
                  ·
                    refine ⟨3318090765486805201932001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17696484082596294410304005 3318090765486805201932001)
                    ·
                      refine ⟨2488568074115103901449001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3318090765486805201932001 2488568074115103901449001)
                      ·
                        rfl

theorem cell23_4846469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 4, 2].length) (baseStart_4846469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846469 prefixEnd_4846469 := by exact prefixLift 4846469
  have htrace : WordTrace (prefixWord ++ tailWord_4846469) baseStart_4846469 baseEnd_4846469 := by
    simpa [prefixWord, tailWord_4846469, baseEnd_4846469] using wordTrace_append hprefix tailTrace_4846469
  have hstable : (prefixWord ++ tailWord_4846469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846469).length < 2 ^ (prefixWord ++ tailWord_4846469).sum := by decide
  have hdescent : baseEnd_4846469 < baseStart_4846469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846505 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 2, 5]
def baseStart_4846505 : Nat := 118140960795 + 4846505 * 2 ^ 59
def prefixEnd_4846505 : Nat := 4983230072969 + 3 ^ 40 * 4846505 * 2
def baseEnd_4846505 : Nat := 829528853139555253532945

theorem tailTrace_4846505 : CollatzResearch.WordTrace tailWord_4846505 prefixEnd_4846505 829528853139555253532945 := by
  unfold tailWord_4846505
  simp only [CollatzResearch.WordTrace]
  refine ⟨176766559306947577001180969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117844372871298384667453979 176766559306947577001180969)
  ·
    refine ⟨132574919480210682750885727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176766559306947577001180969 132574919480210682750885727)
    ·
      refine ⟨198862379220316024126328591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132574919480210682750885727 198862379220316024126328591)
      ·
        refine ⟨298293568830474036189492887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198862379220316024126328591 298293568830474036189492887)
        ·
          refine ⟨447440353245711054284239331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298293568830474036189492887 447440353245711054284239331)
          ·
            refine ⟨671160529868566581426358997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447440353245711054284239331 671160529868566581426358997)
            ·
              refine ⟨15730324918794529252180289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 671160529868566581426358997 15730324918794529252180289)
              ·
                refine ⟨11797743689095896939135217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15730324918794529252180289 11797743689095896939135217)
                ·
                  refine ⟨8848307766821922704351413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11797743689095896939135217 8848307766821922704351413)
                  ·
                    refine ⟨829528853139555253532945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8848307766821922704351413 829528853139555253532945)
                    ·
                      rfl

theorem cell23_4846505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 5].length) (baseStart_4846505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846505 prefixEnd_4846505 := by exact prefixLift 4846505
  have htrace : WordTrace (prefixWord ++ tailWord_4846505) baseStart_4846505 baseEnd_4846505 := by
    simpa [prefixWord, tailWord_4846505, baseEnd_4846505] using wordTrace_append hprefix tailTrace_4846505
  have hstable : (prefixWord ++ tailWord_4846505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846505).length < 2 ^ (prefixWord ++ tailWord_4846505).sum := by decide
  have hdescent : baseEnd_4846505 < baseStart_4846505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846542 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_4846542 : Nat := 118140960795 + 4846542 * 2 ^ 59
def prefixEnd_4846542 : Nat := 4983230072969 + 3 ^ 40 * 4846542 * 2
def baseEnd_4846542 : Nat := 2488605558202882115836165

theorem tailTrace_4846542 : CollatzResearch.WordTrace tailWord_4846542 prefixEnd_4846542 2488605558202882115836165 := by
  unfold tailWord_4846542
  simp only [CollatzResearch.WordTrace]
  refine ⟨22095988600976691540034735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117845272538542354880185253 22095988600976691540034735)
  ·
    refine ⟨33143982901465037310052103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22095988600976691540034735 33143982901465037310052103)
    ·
      refine ⟨49715974352197555965078155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33143982901465037310052103 49715974352197555965078155)
      ·
        refine ⟨74573961528296333947617233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49715974352197555965078155 74573961528296333947617233)
        ·
          refine ⟨55930471146222250460712925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74573961528296333947617233 55930471146222250460712925)
          ·
            refine ⟨20973926679833343922767347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55930471146222250460712925 20973926679833343922767347)
            ·
              refine ⟨31460890019750015884151021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20973926679833343922767347 31460890019750015884151021)
              ·
                refine ⟨11797833757406255956556633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31460890019750015884151021 11797833757406255956556633)
                ·
                  refine ⟨8848375318054691967417475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11797833757406255956556633 8848375318054691967417475)
                  ·
                    refine ⟨13272562977082037951126213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8848375318054691967417475 13272562977082037951126213)
                    ·
                      refine ⟨2488605558202882115836165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13272562977082037951126213 2488605558202882115836165)
                      ·
                        rfl

theorem cell23_4846542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_4846542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846542 prefixEnd_4846542 := by exact prefixLift 4846542
  have htrace : WordTrace (prefixWord ++ tailWord_4846542) baseStart_4846542 baseEnd_4846542 := by
    simpa [prefixWord, tailWord_4846542, baseEnd_4846542] using wordTrace_append hprefix tailTrace_4846542
  have hstable : (prefixWord ++ tailWord_4846542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846542).length < 2 ^ (prefixWord ++ tailWord_4846542).sum := by decide
  have hdescent : baseEnd_4846542 < baseStart_4846542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846626 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_4846626 : Nat := 118140960795 + 4846626 * 2 ^ 59
def prefixEnd_4846626 : Nat := 4983230072969 + 3 ^ 40 * 4846626 * 2
def baseEnd_4846626 : Nat := 2488648690577859787185779

theorem tailTrace_4846626 : CollatzResearch.WordTrace tailWord_4846626 prefixEnd_4846626 2488648690577859787185779 := by
  unfold tailWord_4846626
  simp only [CollatzResearch.WordTrace]
  refine ⟨44192743134877303666583933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117847315026339476444223821 44192743134877303666583933)
  ·
    refine ⟨16572278675578988874968975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44192743134877303666583933 16572278675578988874968975)
    ·
      refine ⟨24858418013368483312453463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16572278675578988874968975 24858418013368483312453463)
      ·
        refine ⟨37287627020052724968680195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24858418013368483312453463 37287627020052724968680195)
        ·
          refine ⟨55931440530079087453020293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37287627020052724968680195 55931440530079087453020293)
          ·
            refine ⟨10487145099389828897441305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55931440530079087453020293 10487145099389828897441305)
            ·
              refine ⟨7865358824542371673080979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10487145099389828897441305 7865358824542371673080979)
              ·
                refine ⟨11798038236813557509621469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7865358824542371673080979 11798038236813557509621469)
                ·
                  refine ⟨4424264338805084066108051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11798038236813557509621469 4424264338805084066108051)
                  ·
                    refine ⟨6636396508207626099162077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4424264338805084066108051 6636396508207626099162077)
                    ·
                      refine ⟨2488648690577859787185779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6636396508207626099162077 2488648690577859787185779)
                      ·
                        rfl

theorem cell23_4846626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_4846626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846626 prefixEnd_4846626 := by exact prefixLift 4846626
  have htrace : WordTrace (prefixWord ++ tailWord_4846626) baseStart_4846626 baseEnd_4846626 := by
    simpa [prefixWord, tailWord_4846626, baseEnd_4846626] using wordTrace_append hprefix tailTrace_4846626
  have hstable : (prefixWord ++ tailWord_4846626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846626).length < 2 ^ (prefixWord ++ tailWord_4846626).sum := by decide
  have hdescent : baseEnd_4846626 < baseStart_4846626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846646 : List Nat := [5, 1, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_4846646 : Nat := 118140960795 + 4846646 * 2 ^ 59
def prefixEnd_4846646 : Nat := 4983230072969 + 3 ^ 40 * 4846646 * 2
def baseEnd_4846646 : Nat := 829552986730316569645229

theorem tailTrace_4846646 : CollatzResearch.WordTrace tailWord_4846646 prefixEnd_4846646 829552986730316569645229 := by
  unfold tailWord_4846646
  simp only [CollatzResearch.WordTrace]
  refine ⟨11048231374964797380128987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117847801332957838721375861 11048231374964797380128987)
  ·
    refine ⟨16572347062447196070193481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11048231374964797380128987 16572347062447196070193481)
    ·
      refine ⟨12429260296835397052645111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16572347062447196070193481 12429260296835397052645111)
      ·
        refine ⟨18643890445253095578967667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12429260296835397052645111 18643890445253095578967667)
        ·
          refine ⟨27965835667879643368451501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18643890445253095578967667 27965835667879643368451501)
          ·
            refine ⟨10487188375454866263169313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27965835667879643368451501 10487188375454866263169313)
            ·
              refine ⟨7865391281591149697376985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10487188375454866263169313 7865391281591149697376985)
              ·
                refine ⟨5899043461193362273032739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7865391281591149697376985 5899043461193362273032739)
                ·
                  refine ⟨8848565191790043409549109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5899043461193362273032739 8848565191790043409549109)
                  ·
                    refine ⟨829552986730316569645229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8848565191790043409549109 829552986730316569645229)
                    ·
                      rfl

theorem cell23_4846646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_4846646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846646 prefixEnd_4846646 := by exact prefixLift 4846646
  have htrace : WordTrace (prefixWord ++ tailWord_4846646) baseStart_4846646 baseEnd_4846646 := by
    simpa [prefixWord, tailWord_4846646, baseEnd_4846646] using wordTrace_append hprefix tailTrace_4846646
  have hstable : (prefixWord ++ tailWord_4846646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846646).length < 2 ^ (prefixWord ++ tailWord_4846646).sum := by decide
  have hdescent : baseEnd_4846646 < baseStart_4846646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846649 : List Nat := [1, 2, 1, 5, 2, 1, 1, 4, 1, 1, 4]
def baseStart_4846649 : Nat := 118140960795 + 4846649 * 2 ^ 59
def prefixEnd_4846649 : Nat := 4983230072969 + 3 ^ 40 * 4846649 * 2
def baseEnd_4846649 : Nat := 2488660500632913197198173

theorem tailTrace_4846649 : CollatzResearch.WordTrace tailWord_4846649 prefixEnd_4846649 2488660500632913197198173 := by
  unfold tailWord_4846649
  simp only [CollatzResearch.WordTrace]
  refine ⟨176771811418425889594423001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117847874278950593062948667 176771811418425889594423001)
  ·
    refine ⟨132578858563819417195817251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176771811418425889594423001 132578858563819417195817251)
    ·
      refine ⟨198868287845729125793725877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132578858563819417195817251 198868287845729125793725877)
      ·
        refine ⟨18643901985537105543161801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 198868287845729125793725877 18643901985537105543161801)
        ·
          refine ⟨13982926489152829157371351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18643901985537105543161801 13982926489152829157371351)
          ·
            refine ⟨20974389733729243736057027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13982926489152829157371351 20974389733729243736057027)
            ·
              refine ⟨31461584600593865604085541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20974389733729243736057027 31461584600593865604085541)
              ·
                refine ⟨5899047112611349800766039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31461584600593865604085541 5899047112611349800766039)
                ·
                  refine ⟨8848570668917024701149059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5899047112611349800766039 8848570668917024701149059)
                  ·
                    refine ⟨13272856003375537051723589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8848570668917024701149059 13272856003375537051723589)
                    ·
                      refine ⟨2488660500632913197198173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13272856003375537051723589 2488660500632913197198173)
                      ·
                        rfl

theorem cell23_4846649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_4846649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846649 prefixEnd_4846649 := by exact prefixLift 4846649
  have htrace : WordTrace (prefixWord ++ tailWord_4846649) baseStart_4846649 baseEnd_4846649 := by
    simpa [prefixWord, tailWord_4846649, baseEnd_4846649] using wordTrace_append hprefix tailTrace_4846649
  have hstable : (prefixWord ++ tailWord_4846649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846649).length < 2 ^ (prefixWord ++ tailWord_4846649).sum := by decide
  have hdescent : baseEnd_4846649 < baseStart_4846649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846669 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_4846669 : Nat := 118140960795 + 4846669 * 2 ^ 59
def prefixEnd_4846669 : Nat := 4983230072969 + 3 ^ 40 * 4846669 * 2
def baseEnd_4846669 : Nat := 2488670770246003118948081

theorem tailTrace_4846669 : CollatzResearch.WordTrace tailWord_4846669 prefixEnd_4846669 2488670770246003118948081 := by
  unfold tailWord_4846669
  simp only [CollatzResearch.WordTrace]
  refine ⟨176772540878353433010151061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117848360585568955340100707 176772540878353433010151061)
  ·
    refine ⟨8286212853672817172350831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 176772540878353433010151061 8286212853672817172350831)
    ·
      refine ⟨12429319280509225758526247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8286212853672817172350831 12429319280509225758526247)
      ·
        refine ⟨18643978920763838637789371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12429319280509225758526247 18643978920763838637789371)
        ·
          refine ⟨27965968381145757956684057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18643978920763838637789371 27965968381145757956684057)
          ·
            refine ⟨20974476285859318467513043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27965968381145757956684057 20974476285859318467513043)
            ·
              refine ⟨31461714428788977701269565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20974476285859318467513043 31461714428788977701269565)
              ·
                refine ⟨11798142910795866637976087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31461714428788977701269565 11798142910795866637976087)
                ·
                  refine ⟨17697214366193799956964131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11798142910795866637976087 17697214366193799956964131)
                  ·
                    refine ⟨26545821549290699935446197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17697214366193799956964131 26545821549290699935446197)
                    ·
                      refine ⟨2488670770246003118948081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26545821549290699935446197 2488670770246003118948081)
                      ·
                        rfl

theorem cell23_4846669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_4846669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846669 prefixEnd_4846669 := by exact prefixLift 4846669
  have htrace : WordTrace (prefixWord ++ tailWord_4846669) baseStart_4846669 baseEnd_4846669 := by
    simpa [prefixWord, tailWord_4846669, baseEnd_4846669] using wordTrace_append hprefix tailTrace_4846669
  have hstable : (prefixWord ++ tailWord_4846669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846669).length < 2 ^ (prefixWord ++ tailWord_4846669).sum := by decide
  have hdescent : baseEnd_4846669 < baseStart_4846669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846675 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 6]
def baseStart_4846675 : Nat := 118140960795 + 4846675 * 2 ^ 59
def prefixEnd_4846675 : Nat := 4983230072969 + 3 ^ 40 * 4846675 * 2
def baseEnd_4846675 : Nat := 2488673851129930095473053

theorem tailTrace_4846675 : CollatzResearch.WordTrace tailWord_4846675 prefixEnd_4846675 2488673851129930095473053 := by
  unfold tailWord_4846675
  simp only [CollatzResearch.WordTrace]
  refine ⟨176772759716331696034869479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117848506477554464023246319 176772759716331696034869479)
  ·
    refine ⟨265159139574497544052304219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176772759716331696034869479 265159139574497544052304219)
    ·
      refine ⟨397738709361746316078456329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265159139574497544052304219 397738709361746316078456329)
      ·
        refine ⟨298304032021309737058842247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397738709361746316078456329 298304032021309737058842247)
        ·
          refine ⟨447456048031964605588263371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298304032021309737058842247 447456048031964605588263371)
          ·
            refine ⟨671184072047946908382395057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447456048031964605588263371 671184072047946908382395057)
            ·
              refine ⟨503388054035960181286796293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 671184072047946908382395057 503388054035960181286796293)
              ·
                refine ⟨94385260131742533991274305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 503388054035960181286796293 94385260131742533991274305)
                ·
                  refine ⟨70788945098806900493455729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94385260131742533991274305 70788945098806900493455729)
                  ·
                    refine ⟨53091708824105175370091797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70788945098806900493455729 53091708824105175370091797)
                    ·
                      refine ⟨2488673851129930095473053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53091708824105175370091797 2488673851129930095473053)
                      ·
                        rfl

theorem cell23_4846675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_4846675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846675 prefixEnd_4846675 := by exact prefixLift 4846675
  have htrace : WordTrace (prefixWord ++ tailWord_4846675) baseStart_4846675 baseEnd_4846675 := by
    simpa [prefixWord, tailWord_4846675, baseEnd_4846675] using wordTrace_append hprefix tailTrace_4846675
  have hstable : (prefixWord ++ tailWord_4846675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846675).length < 2 ^ (prefixWord ++ tailWord_4846675).sum := by decide
  have hdescent : baseEnd_4846675 < baseStart_4846675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846682 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3]
def baseStart_4846682 : Nat := 118140960795 + 4846682 * 2 ^ 59
def prefixEnd_4846682 : Nat := 4983230072969 + 3 ^ 40 * 4846682 * 2
def baseEnd_4846682 : Nat := 2488677445494511568085521

theorem tailTrace_4846682 : CollatzResearch.WordTrace tailWord_4846682 prefixEnd_4846682 2488677445494511568085521 := by
  unfold tailWord_4846682
  simp only [CollatzResearch.WordTrace]
  refine ⟨44193253756826584057593575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117848676684870890820249533 44193253756826584057593575)
  ·
    refine ⟨66289880635239876086390363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44193253756826584057593575 66289880635239876086390363)
    ·
      refine ⟨99434820952859814129585545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66289880635239876086390363 99434820952859814129585545)
      ·
        refine ⟨74576115714644860597189159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99434820952859814129585545 74576115714644860597189159)
        ·
          refine ⟨111864173571967290895783739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74576115714644860597189159 111864173571967290895783739)
          ·
            refine ⟨167796260357950936343675609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111864173571967290895783739 167796260357950936343675609)
            ·
              refine ⟨125847195268463202257756707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167796260357950936343675609 125847195268463202257756707)
              ·
                refine ⟨188770792902694803386635061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125847195268463202257756707 188770792902694803386635061)
                ·
                  refine ⟨17697261834627637817497037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188770792902694803386635061 17697261834627637817497037)
                  ·
                    refine ⟨6636473187985364181561389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17697261834627637817497037 6636473187985364181561389)
                    ·
                      refine ⟨2488677445494511568085521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6636473187985364181561389 2488677445494511568085521)
                      ·
                        rfl

theorem cell23_4846682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_4846682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846682 prefixEnd_4846682 := by exact prefixLift 4846682
  have htrace : WordTrace (prefixWord ++ tailWord_4846682) baseStart_4846682 baseEnd_4846682 := by
    simpa [prefixWord, tailWord_4846682, baseEnd_4846682] using wordTrace_append hprefix tailTrace_4846682
  have hstable : (prefixWord ++ tailWord_4846682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846682).length < 2 ^ (prefixWord ++ tailWord_4846682).sum := by decide
  have hdescent : baseEnd_4846682 < baseStart_4846682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846756 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 1, 4, 2]
def baseStart_4846756 : Nat := 118140960795 + 4846756 * 2 ^ 59
def prefixEnd_4846756 : Nat := 4983230072969 + 3 ^ 40 * 4846756 * 2
def baseEnd_4846756 : Nat := 2488715443062944278560181

theorem tailTrace_4846756 : CollatzResearch.WordTrace tailWord_4846756 prefixEnd_4846756 2488715443062944278560181 := by
  unfold tailWord_4846756
  simp only [CollatzResearch.WordTrace]
  refine ⟨88387857014519123434284061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117850476019358831245712081 88387857014519123434284061)
  ·
    refine ⟨33145446380444671287856523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88387857014519123434284061 33145446380444671287856523)
    ·
      refine ⟨49718169570667006931784785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33145446380444671287856523 49718169570667006931784785)
      ·
        refine ⟨37288627178000255198838589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49718169570667006931784785 37288627178000255198838589)
        ·
          refine ⟨13983235191750095699564471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37288627178000255198838589 13983235191750095699564471)
          ·
            refine ⟨20974852787625143549346707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13983235191750095699564471 20974852787625143549346707)
            ·
              refine ⟨31462279181437715324020061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20974852787625143549346707 31462279181437715324020061)
              ·
                refine ⟨11798354693039143246507523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31462279181437715324020061 11798354693039143246507523)
                ·
                  refine ⟨17697532039558714869761285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11798354693039143246507523 17697532039558714869761285)
                  ·
                    refine ⟨3318287257417259038080241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17697532039558714869761285 3318287257417259038080241)
                    ·
                      refine ⟨2488715443062944278560181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3318287257417259038080241 2488715443062944278560181)
                      ·
                        rfl

theorem cell23_4846756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_4846756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846756 prefixEnd_4846756 := by exact prefixLift 4846756
  have htrace : WordTrace (prefixWord ++ tailWord_4846756) baseStart_4846756 baseEnd_4846756 := by
    simpa [prefixWord, tailWord_4846756, baseEnd_4846756] using wordTrace_append hprefix tailTrace_4846756
  have hstable : (prefixWord ++ tailWord_4846756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846756).length < 2 ^ (prefixWord ++ tailWord_4846756).sum := by decide
  have hdescent : baseEnd_4846756 < baseStart_4846756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846799 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 2, 5, 2]
def baseStart_4846799 : Nat := 118140960795 + 4846799 * 2 ^ 59
def prefixEnd_4846799 : Nat := 4983230072969 + 3 ^ 40 * 4846799 * 2
def baseEnd_4846799 : Nat := 2488737522731087610322483

theorem tailTrace_4846799 : CollatzResearch.WordTrace tailWord_4846799 prefixEnd_4846799 2488737522731087610322483 := by
  unfold tailWord_4846799
  simp only [CollatzResearch.WordTrace]
  refine ⟨176777282367882465212383451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117851521578588310141588967 176777282367882465212383451)
  ·
    refine ⟨265165923551823697818575177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176777282367882465212383451 265165923551823697818575177)
    ·
      refine ⟨198874442663867773363931383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265165923551823697818575177 198874442663867773363931383)
      ·
        refine ⟨298311663995801660045897075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198874442663867773363931383 298311663995801660045897075)
        ·
          refine ⟨447467495993702490068845613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298311663995801660045897075 447467495993702490068845613)
          ·
            refine ⟨167800310997638433775817105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 447467495993702490068845613 167800310997638433775817105)
            ·
              refine ⟨125850233248228825331862829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167800310997638433775817105 125850233248228825331862829)
              ·
                refine ⟨47193837468085809499448561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125850233248228825331862829 47193837468085809499448561)
                ·
                  refine ⟨35395378101064357124586421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47193837468085809499448561 35395378101064357124586421)
                  ·
                    refine ⟨3318316696974783480429977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35395378101064357124586421 3318316696974783480429977)
                    ·
                      refine ⟨2488737522731087610322483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3318316696974783480429977 2488737522731087610322483)
                      ·
                        rfl

theorem cell23_4846799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 5, 2].length) (baseStart_4846799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846799 prefixEnd_4846799 := by exact prefixLift 4846799
  have htrace : WordTrace (prefixWord ++ tailWord_4846799) baseStart_4846799 baseEnd_4846799 := by
    simpa [prefixWord, tailWord_4846799, baseEnd_4846799] using wordTrace_append hprefix tailTrace_4846799
  have hstable : (prefixWord ++ tailWord_4846799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846799).length < 2 ^ (prefixWord ++ tailWord_4846799).sum := by decide
  have hdescent : baseEnd_4846799 < baseStart_4846799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846832 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 5]
def baseStart_4846832 : Nat := 118140960795 + 4846832 * 2 ^ 59
def prefixEnd_4846832 : Nat := 4983230072969 + 3 ^ 40 * 4846832 * 2
def baseEnd_4846832 : Nat := 2488754467592685981209831

theorem tailTrace_4846832 : CollatzResearch.WordTrace tailWord_4846832 prefixEnd_4846832 2488754467592685981209831 := by
  unfold tailWord_4846832
  simp only [CollatzResearch.WordTrace]
  refine ⟨88389242988381455924167375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117852323984508607898889833 88389242988381455924167375)
  ·
    refine ⟨132583864482572183886251063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88389242988381455924167375 132583864482572183886251063)
    ·
      refine ⟨198875796723858275829376595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132583864482572183886251063 198875796723858275829376595)
      ·
        refine ⟨298313695085787413744064893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198875796723858275829376595 298313695085787413744064893)
        ·
          refine ⟨111867635657170280154024335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 298313695085787413744064893 111867635657170280154024335)
          ·
            refine ⟨167801453485755420231036503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111867635657170280154024335 167801453485755420231036503)
            ·
              refine ⟨251702180228633130346554755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167801453485755420231036503 251702180228633130346554755)
              ·
                refine ⟨377553270342949695519832133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251702180228633130346554755 377553270342949695519832133)
                ·
                  refine ⟨70791238189303067909968525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377553270342949695519832133 70791238189303067909968525)
                  ·
                    refine ⟨26546714320988650466238197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70791238189303067909968525 26546714320988650466238197)
                    ·
                      refine ⟨2488754467592685981209831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26546714320988650466238197 2488754467592685981209831)
                      ·
                        rfl

theorem cell23_4846832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_4846832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846832 prefixEnd_4846832 := by exact prefixLift 4846832
  have htrace : WordTrace (prefixWord ++ tailWord_4846832) baseStart_4846832 baseEnd_4846832 := by
    simpa [prefixWord, tailWord_4846832, baseEnd_4846832] using wordTrace_append hprefix tailTrace_4846832
  have hstable : (prefixWord ++ tailWord_4846832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846832).length < 2 ^ (prefixWord ++ tailWord_4846832).sum := by decide
  have hdescent : baseEnd_4846832 < baseStart_4846832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846846 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_4846846 : Nat := 118140960795 + 4846846 * 2 ^ 59
def prefixEnd_4846846 : Nat := 4983230072969 + 3 ^ 40 * 4846846 * 2
def baseEnd_4846846 : Nat := 2488761656321848926434767

theorem tailTrace_4846846 : CollatzResearch.WordTrace tailWord_4846846 prefixEnd_4846846 2488761656321848926434767 := by
  unfold tailWord_4846846
  simp only [CollatzResearch.WordTrace]
  refine ⟨22097374574839024029918049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117852664399141461492896261 22097374574839024029918049)
  ·
    refine ⟨16573030931129268022438537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22097374574839024029918049 16573030931129268022438537)
    ·
      refine ⟨12429773198346951016828903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16573030931129268022438537 12429773198346951016828903)
      ·
        refine ⟨18644659797520426525243355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12429773198346951016828903 18644659797520426525243355)
        ·
          refine ⟨27966989696280639787865033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18644659797520426525243355 27966989696280639787865033)
          ·
            refine ⟨20975242272210479840898775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27966989696280639787865033 20975242272210479840898775)
            ·
              refine ⟨31462863408315719761348163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20975242272210479840898775 31462863408315719761348163)
              ·
                refine ⟨47194295112473579642022245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31462863408315719761348163 47194295112473579642022245)
                ·
                  refine ⟨8848930333588796182879171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47194295112473579642022245 8848930333588796182879171)
                  ·
                    refine ⟨13273395500383194274318757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8848930333588796182879171 13273395500383194274318757)
                    ·
                      refine ⟨2488761656321848926434767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13273395500383194274318757 2488761656321848926434767)
                      ·
                        rfl

theorem cell23_4846846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_4846846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846846 prefixEnd_4846846 := by exact prefixLift 4846846
  have htrace : WordTrace (prefixWord ++ tailWord_4846846) baseStart_4846846 baseEnd_4846846 := by
    simpa [prefixWord, tailWord_4846846, baseEnd_4846846] using wordTrace_append hprefix tailTrace_4846846
  have hstable : (prefixWord ++ tailWord_4846846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846846).length < 2 ^ (prefixWord ++ tailWord_4846846).sum := by decide
  have hdescent : baseEnd_4846846 < baseStart_4846846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846936 : List Nat := [2, 1, 2, 2, 1, 1, 4, 4, 1, 1, 4]
def baseStart_4846936 : Nat := 118140960795 + 4846936 * 2 ^ 59
def prefixEnd_4846936 : Nat := 4983230072969 + 3 ^ 40 * 4846936 * 2
def baseEnd_4846936 : Nat := 2488807869580753574309353

theorem tailTrace_4846936 : CollatzResearch.WordTrace tailWord_4846936 prefixEnd_4846936 2488807869580753574309353 := by
  unfold tailWord_4846936
  simp only [CollatzResearch.WordTrace]
  refine ⟨88391139584193068805060331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117854852778924091740080441 88391139584193068805060331)
  ·
    refine ⟨132586709376289603207590497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88391139584193068805060331 132586709376289603207590497)
    ·
      refine ⟨99440032032217202405692873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132586709376289603207590497 99440032032217202405692873)
      ·
        refine ⟨74580024024162901804269655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99440032032217202405692873 74580024024162901804269655)
        ·
          refine ⟨111870036036244352706404483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74580024024162901804269655 111870036036244352706404483)
          ·
            refine ⟨167805054054366529059606725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111870036036244352706404483 167805054054366529059606725)
            ·
              refine ⟨31463447635193724198676261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167805054054366529059606725 31463447635193724198676261)
              ·
                refine ⟨5899396431598823287251799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31463447635193724198676261 5899396431598823287251799)
                ·
                  refine ⟨8849094647398234930877699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5899396431598823287251799 8849094647398234930877699)
                  ·
                    refine ⟨13273641971097352396316549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8849094647398234930877699 13273641971097352396316549)
                    ·
                      refine ⟨2488807869580753574309353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13273641971097352396316549 2488807869580753574309353)
                      ·
                        rfl

theorem cell23_4846936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_4846936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846936 prefixEnd_4846936 := by exact prefixLift 4846936
  have htrace : WordTrace (prefixWord ++ tailWord_4846936) baseStart_4846936 baseEnd_4846936 := by
    simpa [prefixWord, tailWord_4846936, baseEnd_4846936] using wordTrace_append hprefix tailTrace_4846936
  have hstable : (prefixWord ++ tailWord_4846936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846936).length < 2 ^ (prefixWord ++ tailWord_4846936).sum := by decide
  have hdescent : baseEnd_4846936 < baseStart_4846936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846946 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_4846946 : Nat := 118140960795 + 4846946 * 2 ^ 59
def prefixEnd_4846946 : Nat := 4983230072969 + 3 ^ 40 * 4846946 * 2
def baseEnd_4846946 : Nat := 829604334795766178394769

theorem tailTrace_4846946 : CollatzResearch.WordTrace tailWord_4846946 prefixEnd_4846946 829604334795766178394769 := by
  unfold tailWord_4846946
  simp only [CollatzResearch.WordTrace]
  refine ⟨44195660974587477329496173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117855095932233272878656461 44195660974587477329496173)
  ·
    refine ⟨16573372865470303998561065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44195660974587477329496173 16573372865470303998561065)
    ·
      refine ⟨12430029649102727998920799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16573372865470303998561065 12430029649102727998920799)
      ·
        refine ⟨18645044473654091998381199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12430029649102727998920799 18645044473654091998381199)
        ·
          refine ⟨27967566710481137997571799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18645044473654091998381199 27967566710481137997571799)
          ·
            refine ⟨41951350065721706996357699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27967566710481137997571799 41951350065721706996357699)
            ·
              refine ⟨62927025098582560494536549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41951350065721706996357699 62927025098582560494536549)
              ·
                refine ⟨11798817205984230092725603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62927025098582560494536549 11798817205984230092725603)
                ·
                  refine ⟨17698225808976345139088405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11798817205984230092725603 17698225808976345139088405)
                  ·
                    refine ⟨829604334795766178394769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17698225808976345139088405 829604334795766178394769)
                    ·
                      rfl

theorem cell23_4846946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_4846946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846946 prefixEnd_4846946 := by exact prefixLift 4846946
  have htrace : WordTrace (prefixWord ++ tailWord_4846946) baseStart_4846946 baseEnd_4846946 := by
    simpa [prefixWord, tailWord_4846946, baseEnd_4846946] using wordTrace_append hprefix tailTrace_4846946
  have hstable : (prefixWord ++ tailWord_4846946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846946).length < 2 ^ (prefixWord ++ tailWord_4846946).sum := by decide
  have hdescent : baseEnd_4846946 < baseStart_4846946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846980 : List Nat := [2, 3, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_4846980 : Nat := 118140960795 + 4846980 * 2 ^ 59
def prefixEnd_4846980 : Nat := 4983230072969 + 3 ^ 40 * 4846980 * 2
def baseEnd_4846980 : Nat := 829610154243183800719717

theorem tailTrace_4846980 : CollatzResearch.WordTrace tailWord_4846980 prefixEnd_4846980 829610154243183800719717 := by
  unfold tailWord_4846980
  simp only [CollatzResearch.WordTrace]
  refine ⟨88391941990113366562361197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117855922653484488749814929 88391941990113366562361197)
  ·
    refine ⟨33146978246292512460885449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88391941990113366562361197 33146978246292512460885449)
    ·
      refine ⟨24860233684719384345664087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33146978246292512460885449 24860233684719384345664087)
      ·
        refine ⟨37290350527079076518496131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24860233684719384345664087 37290350527079076518496131)
        ·
          refine ⟨55935525790618614777744197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37290350527079076518496131 55935525790618614777744197)
          ·
            refine ⟨10487911085740990270827037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55935525790618614777744197 10487911085740990270827037)
            ·
              refine ⟨3932966657152871351560139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10487911085740990270827037 3932966657152871351560139)
              ·
                refine ⟨5899449985729307027340209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3932966657152871351560139 5899449985729307027340209)
                ·
                  refine ⟨4424587489296980270505157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5899449985729307027340209 4424587489296980270505157)
                  ·
                    refine ⟨829610154243183800719717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4424587489296980270505157 829610154243183800719717)
                    ·
                      rfl

theorem cell23_4846980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_4846980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846980 prefixEnd_4846980 := by exact prefixLift 4846980
  have htrace : WordTrace (prefixWord ++ tailWord_4846980) baseStart_4846980 baseEnd_4846980 := by
    simpa [prefixWord, tailWord_4846980, baseEnd_4846980] using wordTrace_append hprefix tailTrace_4846980
  have hstable : (prefixWord ++ tailWord_4846980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846980).length < 2 ^ (prefixWord ++ tailWord_4846980).sum := by decide
  have hdescent : baseEnd_4846980 < baseStart_4846980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4846983 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_4846983 : Nat := 118140960795 + 4846983 * 2 ^ 59
def prefixEnd_4846983 : Nat := 4983230072969 + 3 ^ 40 * 4846983 * 2
def baseEnd_4846983 : Nat := 2488832003171514890421637

theorem tailTrace_4846983 : CollatzResearch.WordTrace tailWord_4846983 prefixEnd_4846983 2488832003171514890421637 := by
  unfold tailWord_4846983
  simp only [CollatzResearch.WordTrace]
  refine ⟨176783993399215864637081603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117855995599477243091387735 176783993399215864637081603)
  ·
    refine ⟨265175990098823796955622405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176783993399215864637081603 265175990098823796955622405)
    ·
      refine ⟨49720498143529461929179201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265175990098823796955622405 49720498143529461929179201)
      ·
        refine ⟨37290373607647096446884401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49720498143529461929179201 37290373607647096446884401)
        ·
          refine ⟨27967780205735322335163301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37290373607647096446884401 27967780205735322335163301)
          ·
            refine ⟨5243958788575372937843119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27967780205735322335163301 5243958788575372937843119)
            ·
              refine ⟨7865938182863059406764679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5243958788575372937843119 7865938182863059406764679)
              ·
                refine ⟨11798907274294589110147019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7865938182863059406764679 11798907274294589110147019)
                ·
                  refine ⟨17698360911441883665220529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11798907274294589110147019 17698360911441883665220529)
                  ·
                    refine ⟨13273770683581412748915397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17698360911441883665220529 13273770683581412748915397)
                    ·
                      refine ⟨2488832003171514890421637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13273770683581412748915397 2488832003171514890421637)
                      ·
                        rfl

theorem cell23_4846983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_4846983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4846983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4846983 prefixEnd_4846983 := by exact prefixLift 4846983
  have htrace : WordTrace (prefixWord ++ tailWord_4846983) baseStart_4846983 baseEnd_4846983 := by
    simpa [prefixWord, tailWord_4846983, baseEnd_4846983] using wordTrace_append hprefix tailTrace_4846983
  have hstable : (prefixWord ++ tailWord_4846983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4846983).length < 2 ^ (prefixWord ++ tailWord_4846983).sum := by decide
  have hdescent : baseEnd_4846983 < baseStart_4846983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4846983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847021 : List Nat := [1, 5, 2, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_4847021 : Nat := 118140960795 + 4847021 * 2 ^ 59
def prefixEnd_4847021 : Nat := 4983230072969 + 3 ^ 40 * 4847021 * 2
def baseEnd_4847021 : Nat := 2488851515436385741746463

theorem tailTrace_4847021 : CollatzResearch.WordTrace tailWord_4847021 prefixEnd_4847021 2488851515436385741746463 := by
  unfold tailWord_4847021
  simp only [CollatzResearch.WordTrace]
  refine ⟨176785379373078197126964917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117856919582052131417976611 176785379373078197126964917)
  ·
    refine ⟨16573629316226080980652961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176785379373078197126964917 16573629316226080980652961)
    ·
      refine ⟨12430221987169560735489721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16573629316226080980652961 12430221987169560735489721)
      ·
        refine ⟨9322666490377170551617291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12430221987169560735489721 9322666490377170551617291)
        ·
          refine ⟨13983999735565755827425937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9322666490377170551617291 13983999735565755827425937)
          ·
            refine ⟨10487999801674316870569453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13983999735565755827425937 10487999801674316870569453)
            ·
              refine ⟨3932999925627868826463545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10487999801674316870569453 3932999925627868826463545)
              ·
                refine ⟨2949749944220901619847659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3932999925627868826463545 2949749944220901619847659)
                ·
                  refine ⟨4424624916331352429771489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2949749944220901619847659 4424624916331352429771489)
                  ·
                    refine ⟨3318468687248514322328617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4424624916331352429771489 3318468687248514322328617)
                    ·
                      refine ⟨2488851515436385741746463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3318468687248514322328617 2488851515436385741746463)
                      ·
                        rfl

theorem cell23_4847021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_4847021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847021 prefixEnd_4847021 := by exact prefixLift 4847021
  have htrace : WordTrace (prefixWord ++ tailWord_4847021) baseStart_4847021 baseEnd_4847021 := by
    simpa [prefixWord, tailWord_4847021, baseEnd_4847021] using wordTrace_append hprefix tailTrace_4847021
  have hstable : (prefixWord ++ tailWord_4847021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847021).length < 2 ^ (prefixWord ++ tailWord_4847021).sum := by decide
  have hdescent : baseEnd_4847021 < baseStart_4847021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847039 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 6]
def baseStart_4847039 : Nat := 118140960795 + 4847039 * 2 ^ 59
def prefixEnd_4847039 : Nat := 4983230072969 + 3 ^ 40 * 4847039 * 2
def baseEnd_4847039 : Nat := 2488860758088166671321379

theorem tailTrace_4847039 : CollatzResearch.WordTrace tailWord_4847039 prefixEnd_4847039 2488860758088166671321379 := by
  unfold tailWord_4847039
  simp only [CollatzResearch.WordTrace]
  refine ⟨176786035887012986201120171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117857357258008657467413447 176786035887012986201120171)
  ·
    refine ⟨265179053830519479301680257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176786035887012986201120171 265179053830519479301680257)
    ·
      refine ⟨198884290372889609476260193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265179053830519479301680257 198884290372889609476260193)
      ·
        refine ⟨149163217779667207107195145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198884290372889609476260193 149163217779667207107195145)
        ·
          refine ⟨111872413334750405330396359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149163217779667207107195145 111872413334750405330396359)
          ·
            refine ⟨167808620002125607995594539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111872413334750405330396359 167808620002125607995594539)
            ·
              refine ⟨251712930003188411993391809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167808620002125607995594539 251712930003188411993391809)
              ·
                refine ⟨188784697502391308995043857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251712930003188411993391809 188784697502391308995043857)
                ·
                  refine ⟨141588523126793481746282893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188784697502391308995043857 141588523126793481746282893)
                  ·
                    refine ⟨53095696172547555654856085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 141588523126793481746282893 53095696172547555654856085)
                    ·
                      refine ⟨2488860758088166671321379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53095696172547555654856085 2488860758088166671321379)
                      ·
                        rfl

theorem cell23_4847039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_4847039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847039 prefixEnd_4847039 := by exact prefixLift 4847039
  have htrace : WordTrace (prefixWord ++ tailWord_4847039) baseStart_4847039 baseEnd_4847039 := by
    simpa [prefixWord, tailWord_4847039, baseEnd_4847039] using wordTrace_append hprefix tailTrace_4847039
  have hstable : (prefixWord ++ tailWord_4847039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847039).length < 2 ^ (prefixWord ++ tailWord_4847039).sum := by decide
  have hdescent : baseEnd_4847039 < baseStart_4847039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847049 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 9]
def baseStart_4847049 : Nat := 118140960795 + 4847049 * 2 ^ 59
def prefixEnd_4847049 : Nat := 4983230072969 + 3 ^ 40 * 4847049 * 2
def baseEnd_4847049 : Nat := 276540654766079070244037

theorem tailTrace_4847049 : CollatzResearch.WordTrace tailWord_4847049 prefixEnd_4847049 276540654766079070244037 := by
  unfold tailWord_4847049
  simp only [CollatzResearch.WordTrace]
  refine ⟨176786400616976757908984201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117857600411317838605989467 176786400616976757908984201)
  ·
    refine ⟨132589800462732568431738151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176786400616976757908984201 132589800462732568431738151)
    ·
      refine ⟨198884700694098852647607227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132589800462732568431738151 198884700694098852647607227)
      ·
        refine ⟨298327051041148278971410841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198884700694098852647607227 298327051041148278971410841)
        ·
          refine ⟨223745288280861209228558131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298327051041148278971410841 223745288280861209228558131)
          ·
            refine ⟨335617932421291813842837197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223745288280861209228558131 335617932421291813842837197)
            ·
              refine ⟨125856724657984430191063949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 335617932421291813842837197 125856724657984430191063949)
              ·
                refine ⟨47196271746744161321648981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125856724657984430191063949 47196271746744161321648981)
                ·
                  refine ⟨276540654766079070244037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47196271746744161321648981 276540654766079070244037)
                  ·
                    rfl

theorem cell23_4847049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 9].length) (baseStart_4847049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847049 prefixEnd_4847049 := by exact prefixLift 4847049
  have htrace : WordTrace (prefixWord ++ tailWord_4847049) baseStart_4847049 baseEnd_4847049 := by
    simpa [prefixWord, tailWord_4847049, baseEnd_4847049] using wordTrace_append hprefix tailTrace_4847049
  have hstable : (prefixWord ++ tailWord_4847049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847049).length < 2 ^ (prefixWord ++ tailWord_4847049).sum := by decide
  have hdescent : baseEnd_4847049 < baseStart_4847049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847076 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_4847076 : Nat := 118140960795 + 4847076 * 2 ^ 59
def prefixEnd_4847076 : Nat := 4983230072969 + 3 ^ 40 * 4847076 * 2
def baseEnd_4847076 : Nat := 2488879756872383026558709

theorem tailTrace_4847076 : CollatzResearch.WordTrace tailWord_4847076 prefixEnd_4847076 2488879756872383026558709 := by
  unfold tailWord_4847076
  simp only [CollatzResearch.WordTrace]
  refine ⟨88393692693939470760108541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117858256925252627680144721 88393692693939470760108541)
  ·
    refine ⟨33147634760227301535040703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88393692693939470760108541 33147634760227301535040703)
    ·
      refine ⟨49721452140340952302561055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33147634760227301535040703 49721452140340952302561055)
      ·
        refine ⟨74582178210511428453841583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49721452140340952302561055 74582178210511428453841583)
        ·
          refine ⟨111873267315767142680762375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74582178210511428453841583 111873267315767142680762375)
          ·
            refine ⟨167809900973650714021143563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111873267315767142680762375 167809900973650714021143563)
            ·
              refine ⟨251714851460476071031715345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167809900973650714021143563 251714851460476071031715345)
              ·
                refine ⟨188786138595357053273786509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251714851460476071031715345 188786138595357053273786509)
                ·
                  refine ⟨70794801973258894977669941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188786138595357053273786509 70794801973258894977669941)
                  ·
                    refine ⟨6637012684993021404156557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70794801973258894977669941 6637012684993021404156557)
                    ·
                      refine ⟨2488879756872383026558709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6637012684993021404156557 2488879756872383026558709)
                      ·
                        rfl

theorem cell23_4847076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_4847076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847076 prefixEnd_4847076 := by exact prefixLift 4847076
  have htrace : WordTrace (prefixWord ++ tailWord_4847076) baseStart_4847076 baseEnd_4847076 := by
    simpa [prefixWord, tailWord_4847076, baseEnd_4847076] using wordTrace_append hprefix tailTrace_4847076
  have hstable : (prefixWord ++ tailWord_4847076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847076).length < 2 ^ (prefixWord ++ tailWord_4847076).sum := by decide
  have hdescent : baseEnd_4847076 < baseStart_4847076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847077 : List Nat := [1, 3, 1, 5, 1, 1, 1, 4, 2, 2, 2]
def baseStart_4847077 : Nat := 118140960795 + 4847077 * 2 ^ 59
def prefixEnd_4847077 : Nat := 4983230072969 + 3 ^ 40 * 4847077 * 2
def baseEnd_4847077 : Nat := 2488880270353037522646205

theorem tailTrace_4847077 : CollatzResearch.WordTrace tailWord_4847077 prefixEnd_4847077 2488880270353037522646205 := by
  unfold tailWord_4847077
  simp only [CollatzResearch.WordTrace]
  refine ⟨176787421860875318691003485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117858281240583545794002323 176787421860875318691003485)
  ·
    refine ⟨66295283197828244509126307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176787421860875318691003485 66295283197828244509126307)
    ·
      refine ⟨99442924796742366763689461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66295283197828244509126307 99442924796742366763689461)
      ·
        refine ⟨9322774199694596884095887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99442924796742366763689461 9322774199694596884095887)
        ·
          refine ⟨13984161299541895326143831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9322774199694596884095887 13984161299541895326143831)
          ·
            refine ⟨20976241949312842989215747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13984161299541895326143831 20976241949312842989215747)
            ·
              refine ⟨31464362923969264483823621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20976241949312842989215747 31464362923969264483823621)
              ·
                refine ⟨5899568048244237090716929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31464362923969264483823621 5899568048244237090716929)
                ·
                  refine ⟨4424676036183177818037697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5899568048244237090716929 4424676036183177818037697)
                  ·
                    refine ⟨3318507027137383363528273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4424676036183177818037697 3318507027137383363528273)
                    ·
                      refine ⟨2488880270353037522646205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3318507027137383363528273 2488880270353037522646205)
                      ·
                        rfl

theorem cell23_4847077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_4847077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847077 prefixEnd_4847077 := by exact prefixLift 4847077
  have htrace : WordTrace (prefixWord ++ tailWord_4847077) baseStart_4847077 baseEnd_4847077 := by
    simpa [prefixWord, tailWord_4847077, baseEnd_4847077] using wordTrace_append hprefix tailTrace_4847077
  have hstable : (prefixWord ++ tailWord_4847077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847077).length < 2 ^ (prefixWord ++ tailWord_4847077).sum := by decide
  have hdescent : baseEnd_4847077 < baseStart_4847077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847133 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_4847133 : Nat := 118140960795 + 4847133 * 2 ^ 59
def prefixEnd_4847133 : Nat := 4983230072969 + 3 ^ 40 * 4847133 * 2
def baseEnd_4847133 : Nat := 2488909025269689303545947

theorem tailTrace_4847133 : CollatzResearch.WordTrace tailWord_4847133 prefixEnd_4847133 2488909025269689303545947 := by
  unfold tailWord_4847133
  simp only [CollatzResearch.WordTrace]
  refine ⟨176789464348672440255042053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117859642899114960170028035 176789464348672440255042053)
  ·
    refine ⟨33148024565376082547820385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176789464348672440255042053 33148024565376082547820385)
    ·
      refine ⟨24861018424032061910865289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33148024565376082547820385 24861018424032061910865289)
      ·
        refine ⟨18645763818024046433148967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24861018424032061910865289 18645763818024046433148967)
        ·
          refine ⟨27968645727036069649723451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18645763818024046433148967 27968645727036069649723451)
          ·
            refine ⟨41952968590554104474585177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27968645727036069649723451 41952968590554104474585177)
            ·
              refine ⟨31464726442915578355938883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41952968590554104474585177 31464726442915578355938883)
              ·
                refine ⟨47197089664373367533908325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31464726442915578355938883 47197089664373367533908325)
                ·
                  refine ⟨8849454312070006412607811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47197089664373367533908325 8849454312070006412607811)
                  ·
                    refine ⟨13274181468105009618911717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8849454312070006412607811 13274181468105009618911717)
                    ·
                      refine ⟨2488909025269689303545947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13274181468105009618911717 2488909025269689303545947)
                      ·
                        rfl

theorem cell23_4847133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_4847133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847133 prefixEnd_4847133 := by exact prefixLift 4847133
  have htrace : WordTrace (prefixWord ++ tailWord_4847133) baseStart_4847133 baseEnd_4847133 := by
    simpa [prefixWord, tailWord_4847133, baseEnd_4847133] using wordTrace_append hprefix tailTrace_4847133
  have hstable : (prefixWord ++ tailWord_4847133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847133).length < 2 ^ (prefixWord ++ tailWord_4847133).sum := by decide
  have hdescent : baseEnd_4847133 < baseStart_4847133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847134 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 7]
def baseStart_4847134 : Nat := 118140960795 + 4847134 * 2 ^ 59
def prefixEnd_4847134 : Nat := 4983230072969 + 3 ^ 40 * 4847134 * 2
def baseEnd_4847134 : Nat := 276545504305593755514827

theorem tailTrace_4847134 : CollatzResearch.WordTrace tailWord_4847134 prefixEnd_4847134 276545504305593755514827 := by
  unfold tailWord_4847134
  simp only [CollatzResearch.WordTrace]
  refine ⟨22098687602708602178228557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117859667214445878283885637 22098687602708602178228557)
  ·
    refine ⟨8287007851015725816835709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22098687602708602178228557 8287007851015725816835709)
    ·
      refine ⟨3107627944130897181313391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8287007851015725816835709 3107627944130897181313391)
      ·
        refine ⟨4661441916196345771970087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3107627944130897181313391 4661441916196345771970087)
        ·
          refine ⟨6992162874294518657955131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4661441916196345771970087 6992162874294518657955131)
          ·
            refine ⟨10488244311441777986932697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6992162874294518657955131 10488244311441777986932697)
            ·
              refine ⟨7866183233581333490199523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10488244311441777986932697 7866183233581333490199523)
              ·
                refine ⟨11799274850372000235299285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7866183233581333490199523 11799274850372000235299285)
                ·
                  refine ⟨276545504305593755514827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11799274850372000235299285 276545504305593755514827)
                  ·
                    rfl

theorem cell23_4847134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_4847134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847134 prefixEnd_4847134 := by exact prefixLift 4847134
  have htrace : WordTrace (prefixWord ++ tailWord_4847134) baseStart_4847134 baseEnd_4847134 := by
    simpa [prefixWord, tailWord_4847134, baseEnd_4847134] using wordTrace_append hprefix tailTrace_4847134
  have hstable : (prefixWord ++ tailWord_4847134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847134).length < 2 ^ (prefixWord ++ tailWord_4847134).sum := by decide
  have hdescent : baseEnd_4847134 < baseStart_4847134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847233 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 3, 6]
def baseStart_4847233 : Nat := 118140960795 + 4847233 * 2 ^ 59
def prefixEnd_4847233 : Nat := 4983230072969 + 3 ^ 40 * 4847233 * 2
def baseEnd_4847233 : Nat := 829653457778379637431829

theorem tailTrace_4847233 : CollatzResearch.WordTrace tailWord_4847233 prefixEnd_4847233 829653457778379637431829 := by
  unfold tailWord_4847233
  simp only [CollatzResearch.WordTrace]
  refine ⟨176793111648310157333682353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117862074432206771555788235 176793111648310157333682353)
  ·
    refine ⟨132594833736232618000261765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176793111648310157333682353 132594833736232618000261765)
    ·
      refine ⟨24861531325543615875049081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132594833736232618000261765 24861531325543615875049081)
      ·
        refine ⟨18646148494157711906286811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24861531325543615875049081 18646148494157711906286811)
        ·
          refine ⟨27969222741236567859430217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18646148494157711906286811 27969222741236567859430217)
          ·
            refine ⟨20976917055927425894572663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27969222741236567859430217 20976917055927425894572663)
            ·
              refine ⟨31465375583891138841858995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20976917055927425894572663 31465375583891138841858995)
              ·
                refine ⟨47198063375836708262788493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31465375583891138841858995 47198063375836708262788493)
                ·
                  refine ⟨17699273765938765598545685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47198063375836708262788493 17699273765938765598545685)
                  ·
                    refine ⟨829653457778379637431829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17699273765938765598545685 829653457778379637431829)
                    ·
                      rfl

theorem cell23_4847233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_4847233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847233 prefixEnd_4847233 := by exact prefixLift 4847233
  have htrace : WordTrace (prefixWord ++ tailWord_4847233) baseStart_4847233 baseEnd_4847233 := by
    simpa [prefixWord, tailWord_4847233, baseEnd_4847233] using wordTrace_append hprefix tailTrace_4847233
  have hstable : (prefixWord ++ tailWord_4847233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847233).length < 2 ^ (prefixWord ++ tailWord_4847233).sum := by decide
  have hdescent : baseEnd_4847233 < baseStart_4847233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847277 : List Nat := [1, 5, 2, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_4847277 : Nat := 118140960795 + 4847277 * 2 ^ 59
def prefixEnd_4847277 : Nat := 4983230072969 + 3 ^ 40 * 4847277 * 2
def baseEnd_4847277 : Nat := 2488982966483936740145285

theorem tailTrace_4847277 : CollatzResearch.WordTrace tailWord_4847277 prefixEnd_4847277 2488982966483936740145285 := by
  unfold tailWord_4847277
  simp only [CollatzResearch.WordTrace]
  refine ⟨176794716460150752848284085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117863144306767168565522723 176794716460150752848284085)
  ·
    refine ⟨16574504668139133079526633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176794716460150752848284085 16574504668139133079526633)
    ·
      refine ⟨12430878501104349809644975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16574504668139133079526633 12430878501104349809644975)
      ·
        refine ⟨18646317751656524714467463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12430878501104349809644975 18646317751656524714467463)
        ·
          refine ⟨27969476627484787071701195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18646317751656524714467463 27969476627484787071701195)
          ·
            refine ⟨41954214941227180607551793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27969476627484787071701195 41954214941227180607551793)
            ·
              refine ⟨31465661205920385455663845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41954214941227180607551793 31465661205920385455663845)
              ·
                refine ⟨5899811476110072272936971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31465661205920385455663845 5899811476110072272936971)
                ·
                  refine ⟨8849717214165108409405457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5899811476110072272936971 8849717214165108409405457)
                  ·
                    refine ⟨6637287910623831307054093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8849717214165108409405457 6637287910623831307054093)
                    ·
                      refine ⟨2488982966483936740145285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6637287910623831307054093 2488982966483936740145285)
                      ·
                        rfl

theorem cell23_4847277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_4847277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847277 prefixEnd_4847277 := by exact prefixLift 4847277
  have htrace : WordTrace (prefixWord ++ tailWord_4847277) baseStart_4847277 baseEnd_4847277 := by
    simpa [prefixWord, tailWord_4847277, baseEnd_4847277] using wordTrace_append hprefix tailTrace_4847277
  have hstable : (prefixWord ++ tailWord_4847277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847277).length < 2 ^ (prefixWord ++ tailWord_4847277).sum := by decide
  have hdescent : baseEnd_4847277 < baseStart_4847277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847278 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_4847278 : Nat := 118140960795 + 4847278 * 2 ^ 59
def prefixEnd_4847278 : Nat := 4983230072969 + 3 ^ 40 * 4847278 * 2
def baseEnd_4847278 : Nat := 2488983479964591236232781

theorem tailTrace_4847278 : CollatzResearch.WordTrace tailWord_4847278 prefixEnd_4847278 2488983479964591236232781 := by
  unfold tailWord_4847278
  simp only [CollatzResearch.WordTrace]
  refine ⟨22099344116643391252383811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117863168622098086679380325 22099344116643391252383811)
  ·
    refine ⟨33149016174965086878575717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22099344116643391252383811 33149016174965086878575717)
    ·
      refine ⟨6215440532805953789732947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33149016174965086878575717 6215440532805953789732947)
      ·
        refine ⟨9323160799208930684599421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6215440532805953789732947 9323160799208930684599421)
        ·
          refine ⟨3496185299703349006724783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9323160799208930684599421 3496185299703349006724783)
          ·
            refine ⟨5244277949555023510087175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3496185299703349006724783 5244277949555023510087175)
            ·
              refine ⟨7866416924332535265130763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5244277949555023510087175 7866416924332535265130763)
              ·
                refine ⟨11799625386498802897696145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7866416924332535265130763 11799625386498802897696145)
                ·
                  refine ⟨8849719039874102173272109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11799625386498802897696145 8849719039874102173272109)
                  ·
                    refine ⟨3318644639952788314977041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8849719039874102173272109 3318644639952788314977041)
                    ·
                      refine ⟨2488983479964591236232781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3318644639952788314977041 2488983479964591236232781)
                      ·
                        rfl

theorem cell23_4847278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_4847278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847278 prefixEnd_4847278 := by exact prefixLift 4847278
  have htrace : WordTrace (prefixWord ++ tailWord_4847278) baseStart_4847278 baseEnd_4847278 := by
    simpa [prefixWord, tailWord_4847278, baseEnd_4847278] using wordTrace_append hprefix tailTrace_4847278
  have hstable : (prefixWord ++ tailWord_4847278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847278).length < 2 ^ (prefixWord ++ tailWord_4847278).sum := by decide
  have hdescent : baseEnd_4847278 < baseStart_4847278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847290 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3]
def baseStart_4847290 : Nat := 118140960795 + 4847290 * 2 ^ 59
def prefixEnd_4847290 : Nat := 4983230072969 + 3 ^ 40 * 4847290 * 2
def baseEnd_4847290 : Nat := 2488989641732445189282725

theorem tailTrace_4847290 : CollatzResearch.WordTrace tailWord_4847290 prefixEnd_4847290 2488989641732445189282725 := by
  unfold tailWord_4847290
  simp only [CollatzResearch.WordTrace]
  refine ⟨44198797652275914017126831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117863460406069104045671549 44198797652275914017126831)
  ·
    refine ⟨66298196478413871025690247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44198797652275914017126831 66298196478413871025690247)
    ·
      refine ⟨99447294717620806538535371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66298196478413871025690247 99447294717620806538535371)
      ·
        refine ⟨149170942076431209807803057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99447294717620806538535371 149170942076431209807803057)
        ·
          refine ⟨111878206557323407355852293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149170942076431209807803057 111878206557323407355852293)
          ·
            refine ⟨20977163729498138879222305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111878206557323407355852293 20977163729498138879222305)
            ·
              refine ⟨15732872797123604159416729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20977163729498138879222305 15732872797123604159416729)
              ·
                refine ⟨11799654597842703119562547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15732872797123604159416729 11799654597842703119562547)
                ·
                  refine ⟨17699481896764054679343821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11799654597842703119562547 17699481896764054679343821)
                  ·
                    refine ⟨6637305711286520504753933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17699481896764054679343821 6637305711286520504753933)
                    ·
                      refine ⟨2488989641732445189282725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6637305711286520504753933 2488989641732445189282725)
                      ·
                        rfl

theorem cell23_4847290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_4847290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847290 prefixEnd_4847290 := by exact prefixLift 4847290
  have htrace : WordTrace (prefixWord ++ tailWord_4847290) baseStart_4847290 baseEnd_4847290 := by
    simpa [prefixWord, tailWord_4847290, baseEnd_4847290] using wordTrace_append hprefix tailTrace_4847290
  have hstable : (prefixWord ++ tailWord_4847290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847290).length < 2 ^ (prefixWord ++ tailWord_4847290).sum := by decide
  have hdescent : baseEnd_4847290 < baseStart_4847290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847294 : List Nat := [4, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_4847294 : Nat := 118140960795 + 4847294 * 2 ^ 59
def prefixEnd_4847294 : Nat := 4983230072969 + 3 ^ 40 * 4847294 * 2
def baseEnd_4847294 : Nat := 2488991695655063173632707

theorem tailTrace_4847294 : CollatzResearch.WordTrace tailWord_4847294 prefixEnd_4847294 2488991695655063173632707 := by
  unfold tailWord_4847294
  simp only [CollatzResearch.WordTrace]
  refine ⟨22099417062636145593956617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117863557667392776501101957 22099417062636145593956617)
  ·
    refine ⟨16574562796977109195467463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22099417062636145593956617 16574562796977109195467463)
    ·
      refine ⟨24861844195465663793201195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16574562796977109195467463 24861844195465663793201195)
      ·
        refine ⟨37292766293198495689801793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24861844195465663793201195 37292766293198495689801793)
        ·
          refine ⟨27969574719898871767351345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37292766293198495689801793 27969574719898871767351345)
          ·
            refine ⟨20977181039924153825513509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27969574719898871767351345 20977181039924153825513509)
            ·
              refine ⟨3933221444985778842283783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20977181039924153825513509 3933221444985778842283783)
              ·
                refine ⟨5899832167478668263425675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933221444985778842283783 5899832167478668263425675)
                ·
                  refine ⟨8849748251218002395138513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5899832167478668263425675 8849748251218002395138513)
                  ·
                    refine ⟨6637311188413501796353885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8849748251218002395138513 6637311188413501796353885)
                    ·
                      refine ⟨2488991695655063173632707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6637311188413501796353885 2488991695655063173632707)
                      ·
                        rfl

theorem cell23_4847294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_4847294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847294 prefixEnd_4847294 := by exact prefixLift 4847294
  have htrace : WordTrace (prefixWord ++ tailWord_4847294) baseStart_4847294 baseEnd_4847294 := by
    simpa [prefixWord, tailWord_4847294, baseEnd_4847294] using wordTrace_append hprefix tailTrace_4847294
  have hstable : (prefixWord ++ tailWord_4847294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847294).length < 2 ^ (prefixWord ++ tailWord_4847294).sum := by decide
  have hdescent : baseEnd_4847294 < baseStart_4847294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847318 : List Nat := [5, 2, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_4847318 : Nat := 118140960795 + 4847318 * 2 ^ 59
def prefixEnd_4847318 : Nat := 4983230072969 + 3 ^ 40 * 4847318 * 2
def baseEnd_4847318 : Nat := 829668006396923693244199

theorem tailTrace_4847318 : CollatzResearch.WordTrace tailWord_4847318 prefixEnd_4847318 829668006396923693244199 := by
  unfold tailWord_4847318
  simp only [CollatzResearch.WordTrace]
  refine ⟨11049763240812638553157913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117864141235334811233684405 11049763240812638553157913)
  ·
    refine ⟨8287322430609478914868435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11049763240812638553157913 8287322430609478914868435)
    ·
      refine ⟨12430983645914218372302653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8287322430609478914868435 12430983645914218372302653)
      ·
        refine ⟨4661618867217831889613495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12430983645914218372302653 4661618867217831889613495)
        ·
          refine ⟨6992428300826747834420243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4661618867217831889613495 6992428300826747834420243)
          ·
            refine ⟨10488642451240121751630365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6992428300826747834420243 10488642451240121751630365)
            ·
              refine ⟨3933240919215045656861387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10488642451240121751630365 3933240919215045656861387)
              ·
                refine ⟨5899861378822568485292081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933240919215045656861387 5899861378822568485292081)
                ·
                  refine ⟨4424896034116926363969061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5899861378822568485292081 4424896034116926363969061)
                  ·
                    refine ⟨829668006396923693244199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4424896034116926363969061 829668006396923693244199)
                    ·
                      rfl

theorem cell23_4847318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_4847318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847318 prefixEnd_4847318 := by exact prefixLift 4847318
  have htrace : WordTrace (prefixWord ++ tailWord_4847318) baseStart_4847318 baseEnd_4847318 := by
    simpa [prefixWord, tailWord_4847318, baseEnd_4847318] using wordTrace_append hprefix tailTrace_4847318
  have hstable : (prefixWord ++ tailWord_4847318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847318).length < 2 ^ (prefixWord ++ tailWord_4847318).sum := by decide
  have hdescent : baseEnd_4847318 < baseStart_4847318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847347 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 4, 2, 2]
def baseStart_4847347 : Nat := 118140960795 + 4847347 * 2 ^ 59
def prefixEnd_4847347 : Nat := 4983230072969 + 3 ^ 40 * 4847347 * 2
def baseEnd_4847347 : Nat := 2489018910129751466269963

theorem tailTrace_4847347 : CollatzResearch.WordTrace tailWord_4847347 prefixEnd_4847347 2489018910129751466269963 := by
  unfold tailWord_4847347
  simp only [CollatzResearch.WordTrace]
  refine ⟨176797269569897154803332295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117864846379931436535554863 176797269569897154803332295)
  ·
    refine ⟨265195904354845732204998443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176797269569897154803332295 265195904354845732204998443)
    ·
      refine ⟨397793856532268598307497665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265195904354845732204998443 397793856532268598307497665)
      ·
        refine ⟨298345392399201448730623249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397793856532268598307497665 298345392399201448730623249)
        ·
          refine ⟨223759044299401086547967437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298345392399201448730623249 223759044299401086547967437)
          ·
            refine ⟨83909641612275407455487789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223759044299401086547967437 83909641612275407455487789)
            ·
              refine ⟨31466115604603277795807921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83909641612275407455487789 31466115604603277795807921)
              ·
                refine ⟨23599586703452458346855941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31466115604603277795807921 23599586703452458346855941)
                ·
                  refine ⟨4424922506897335940035489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23599586703452458346855941 4424922506897335940035489)
                  ·
                    refine ⟨3318691880173001955026617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4424922506897335940035489 3318691880173001955026617)
                    ·
                      refine ⟨2489018910129751466269963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3318691880173001955026617 2489018910129751466269963)
                      ·
                        rfl

theorem cell23_4847347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 2, 2].length) (baseStart_4847347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847347 prefixEnd_4847347 := by exact prefixLift 4847347
  have htrace : WordTrace (prefixWord ++ tailWord_4847347) baseStart_4847347 baseEnd_4847347 := by
    simpa [prefixWord, tailWord_4847347, baseEnd_4847347] using wordTrace_append hprefix tailTrace_4847347
  have hstable : (prefixWord ++ tailWord_4847347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847347).length < 2 ^ (prefixWord ++ tailWord_4847347).sum := by decide
  have hdescent : baseEnd_4847347 < baseStart_4847347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847350 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_4847350 : Nat := 118140960795 + 4847350 * 2 ^ 59
def prefixEnd_4847350 : Nat := 4983230072969 + 3 ^ 40 * 4847350 * 2
def baseEnd_4847350 : Nat := 2489020450571714954532449

theorem tailTrace_4847350 : CollatzResearch.WordTrace tailWord_4847350 prefixEnd_4847350 2489020450571714954532449 := by
  unfold tailWord_4847350
  simp only [CollatzResearch.WordTrace]
  refine ⟨11049836186805392894730719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117864919325924190877127669 11049836186805392894730719)
  ·
    refine ⟨16574754280208089342096079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11049836186805392894730719 16574754280208089342096079)
    ·
      refine ⟨24862131420312134013144119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16574754280208089342096079 24862131420312134013144119)
      ·
        refine ⟨37293197130468201019716179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24862131420312134013144119 37293197130468201019716179)
        ·
          refine ⟨55939795695702301529574269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37293197130468201019716179 55939795695702301529574269)
          ·
            refine ⟨20977423385888363073590351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55939795695702301529574269 20977423385888363073590351)
            ·
              refine ⟨31466135078832544610385527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20977423385888363073590351 31466135078832544610385527)
              ·
                refine ⟨47199202618248816915578291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31466135078832544610385527 47199202618248816915578291)
                ·
                  refine ⟨70798803927373225373367437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47199202618248816915578291 70798803927373225373367437)
                  ·
                    refine ⟨26549551472764959515012789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70798803927373225373367437 26549551472764959515012789)
                    ·
                      refine ⟨2489020450571714954532449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26549551472764959515012789 2489020450571714954532449)
                      ·
                        rfl

theorem cell23_4847350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_4847350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847350 prefixEnd_4847350 := by exact prefixLift 4847350
  have htrace : WordTrace (prefixWord ++ tailWord_4847350) baseStart_4847350 baseEnd_4847350 := by
    simpa [prefixWord, tailWord_4847350, baseEnd_4847350] using wordTrace_append hprefix tailTrace_4847350
  have hstable : (prefixWord ++ tailWord_4847350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847350).length < 2 ^ (prefixWord ++ tailWord_4847350).sum := by decide
  have hdescent : baseEnd_4847350 < baseStart_4847350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847364 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_4847364 : Nat := 118140960795 + 4847364 * 2 ^ 59
def prefixEnd_4847364 : Nat := 4983230072969 + 3 ^ 40 * 4847364 * 2
def baseEnd_4847364 : Nat := 2489027639300877899757385

theorem tailTrace_4847364 : CollatzResearch.WordTrace tailWord_4847364 prefixEnd_4847364 2489027639300877899757385 := by
  unfold tailWord_4847364
  simp only [CollatzResearch.WordTrace]
  refine ⟨88398944805417783353350573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117865259740557044471134097 88398944805417783353350573)
  ·
    refine ⟨33149604302031668757506465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88398944805417783353350573 33149604302031668757506465)
    ·
      refine ⟨24862203226523751568129849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33149604302031668757506465 24862203226523751568129849)
      ·
        refine ⟨18646652419892813676097387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24862203226523751568129849 18646652419892813676097387)
        ·
          refine ⟨27969978629839220514146081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18646652419892813676097387 27969978629839220514146081)
          ·
            refine ⟨20977483972379415385609561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27969978629839220514146081 20977483972379415385609561)
            ·
              refine ⟨15733112979284561539207171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20977483972379415385609561 15733112979284561539207171)
              ·
                refine ⟨23599669468926842308810757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15733112979284561539207171 23599669468926842308810757)
                ·
                  refine ⟨4424938025423782932902017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23599669468926842308810757 4424938025423782932902017)
                  ·
                    refine ⟨3318703519067837199676513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4424938025423782932902017 3318703519067837199676513)
                    ·
                      refine ⟨2489027639300877899757385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3318703519067837199676513 2489027639300877899757385)
                      ·
                        rfl

theorem cell23_4847364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_4847364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847364 prefixEnd_4847364 := by exact prefixLift 4847364
  have htrace : WordTrace (prefixWord ++ tailWord_4847364) baseStart_4847364 baseEnd_4847364 := by
    simpa [prefixWord, tailWord_4847364, baseEnd_4847364] using wordTrace_append hprefix tailTrace_4847364
  have hstable : (prefixWord ++ tailWord_4847364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847364).length < 2 ^ (prefixWord ++ tailWord_4847364).sum := by decide
  have hdescent : baseEnd_4847364 < baseStart_4847364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847370 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 7]
def baseStart_4847370 : Nat := 118140960795 + 4847370 * 2 ^ 59
def prefixEnd_4847370 : Nat := 4983230072969 + 3 ^ 40 * 4847370 * 2
def baseEnd_4847370 : Nat := 276558968909422764031373

theorem tailTrace_4847370 : CollatzResearch.WordTrace tailWord_4847370 prefixEnd_4847370 276558968909422764031373 := by
  unfold tailWord_4847370
  simp only [CollatzResearch.WordTrace]
  refine ⟨44199527112203457432854891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117865405632542553154279709 44199527112203457432854891)
  ·
    refine ⟨66299290668305186149282337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44199527112203457432854891 66299290668305186149282337)
    ·
      refine ⟨49724468001228889611961753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66299290668305186149282337 49724468001228889611961753)
      ·
        refine ⟨37293351000921667208971315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49724468001228889611961753 37293351000921667208971315)
        ·
          refine ⟨55940026501382500813456973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37293351000921667208971315 55940026501382500813456973)
          ·
            refine ⟨20977509938018437805046365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55940026501382500813456973 20977509938018437805046365)
            ·
              refine ⟨7866566226756914176892387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20977509938018437805046365 7866566226756914176892387)
              ·
                refine ⟨11799849340135371265338581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7866566226756914176892387 11799849340135371265338581)
                ·
                  refine ⟨276558968909422764031373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11799849340135371265338581 276558968909422764031373)
                  ·
                    rfl

theorem cell23_4847370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_4847370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847370 prefixEnd_4847370 := by exact prefixLift 4847370
  have htrace : WordTrace (prefixWord ++ tailWord_4847370) baseStart_4847370 baseEnd_4847370 := by
    simpa [prefixWord, tailWord_4847370, baseEnd_4847370] using wordTrace_append hprefix tailTrace_4847370
  have hstable : (prefixWord ++ tailWord_4847370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847370).length < 2 ^ (prefixWord ++ tailWord_4847370).sum := by decide
  have hdescent : baseEnd_4847370 < baseStart_4847370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847381 : List Nat := [1, 3, 2, 1, 2, 3, 4, 1, 2, 2, 2]
def baseStart_4847381 : Nat := 118140960795 + 4847381 * 2 ^ 59
def prefixEnd_4847381 : Nat := 4983230072969 + 3 ^ 40 * 4847381 * 2
def baseEnd_4847381 : Nat := 2489036368472004333244807

theorem tailTrace_4847381 : CollatzResearch.WordTrace tailWord_4847381 prefixEnd_4847381 2489036368472004333244807 := by
  unfold tailWord_4847381
  simp only [CollatzResearch.WordTrace]
  refine ⟨176798509651773978610069997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117865673101182652406713331 176798509651773978610069997)
  ·
    refine ⟨66299441119415241978776249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176798509651773978610069997 66299441119415241978776249)
    ·
      refine ⟨49724580839561431484082187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66299441119415241978776249 49724580839561431484082187)
      ·
        refine ⟨74586871259342147226123281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49724580839561431484082187 74586871259342147226123281)
        ·
          refine ⟨55940153444506610419592461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74586871259342147226123281 55940153444506610419592461)
          ·
            refine ⟨20977557541689978907347173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55940153444506610419592461 20977557541689978907347173)
            ·
              refine ⟨3933292039066871045127595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20977557541689978907347173 3933292039066871045127595)
              ·
                refine ⟨5899938058600306567691393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933292039066871045127595 5899938058600306567691393)
                ·
                  refine ⟨4424953543950229925768545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5899938058600306567691393 4424953543950229925768545)
                  ·
                    refine ⟨3318715157962672444326409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4424953543950229925768545 3318715157962672444326409)
                    ·
                      refine ⟨2489036368472004333244807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3318715157962672444326409 2489036368472004333244807)
                      ·
                        rfl

theorem cell23_4847381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_4847381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847381 prefixEnd_4847381 := by exact prefixLift 4847381
  have htrace : WordTrace (prefixWord ++ tailWord_4847381) baseStart_4847381 baseEnd_4847381 := by
    simpa [prefixWord, tailWord_4847381, baseEnd_4847381] using wordTrace_append hprefix tailTrace_4847381
  have hstable : (prefixWord ++ tailWord_4847381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847381).length < 2 ^ (prefixWord ++ tailWord_4847381).sum := by decide
  have hdescent : baseEnd_4847381 < baseStart_4847381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847410 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_4847410 : Nat := 118140960795 + 4847410 * 2 ^ 59
def prefixEnd_4847410 : Nat := 4983230072969 + 3 ^ 40 * 4847410 * 2
def baseEnd_4847410 : Nat := 2489051259410984719782173

theorem tailTrace_4847410 : CollatzResearch.WordTrace tailWord_4847410 prefixEnd_4847410 2489051259410984719782173 := by
  unfold tailWord_4847410
  simp only [CollatzResearch.WordTrace]
  refine ⟨44199891842167229140718921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117866378245779277708583789 44199891842167229140718921)
  ·
    refine ⟨33149918881625421855539191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44199891842167229140718921 33149918881625421855539191)
    ·
      refine ⟨49724878322438132783308787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33149918881625421855539191 49724878322438132783308787)
      ·
        refine ⟨74587317483657199174963181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49724878322438132783308787 74587317483657199174963181)
        ·
          refine ⟨27970244056371449690611193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74587317483657199174963181 27970244056371449690611193)
          ·
            refine ⟨20977683042278587267958395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27970244056371449690611193 20977683042278587267958395)
            ·
              refine ⟨31466524563417880901937593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20977683042278587267958395 31466524563417880901937593)
              ·
                refine ⟨23599893422563410676453195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31466524563417880901937593 23599893422563410676453195)
                ·
                  refine ⟨35399840133845116014679793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23599893422563410676453195 35399840133845116014679793)
                  ·
                    refine ⟨26549880100383837011009845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35399840133845116014679793 26549880100383837011009845)
                    ·
                      refine ⟨2489051259410984719782173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26549880100383837011009845 2489051259410984719782173)
                      ·
                        rfl

theorem cell23_4847410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_4847410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847410 prefixEnd_4847410 := by exact prefixLift 4847410
  have htrace : WordTrace (prefixWord ++ tailWord_4847410) baseStart_4847410 baseEnd_4847410 := by
    simpa [prefixWord, tailWord_4847410, baseEnd_4847410] using wordTrace_append hprefix tailTrace_4847410
  have hstable : (prefixWord ++ tailWord_4847410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847410).length < 2 ^ (prefixWord ++ tailWord_4847410).sum := by decide
  have hdescent : baseEnd_4847410 < baseStart_4847410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847421 : List Nat := [1, 4, 1, 4, 1, 3, 2, 2, 5]
def baseStart_4847421 : Nat := 118140960795 + 4847421 * 2 ^ 59
def prefixEnd_4847421 : Nat := 4983230072969 + 3 ^ 40 * 4847421 * 2
def baseEnd_4847421 : Nat := 276561878633131575193847

theorem tailTrace_4847421 : CollatzResearch.WordTrace tailWord_4847421 prefixEnd_4847421 276561878633131575193847 := by
  unfold tailWord_4847421
  simp only [CollatzResearch.WordTrace]
  refine ⟨176799968571629065441526117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117866645714419376961017411 176799968571629065441526117)
  ·
    refine ⟨33149994107180449770286147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176799968571629065441526117 33149994107180449770286147)
    ·
      refine ⟨49724991160770674655429221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33149994107180449770286147 49724991160770674655429221)
      ·
        refine ⟨9323435842644501497892979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49724991160770674655429221 9323435842644501497892979)
        ·
          refine ⟨13985153763966752246839469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9323435842644501497892979 13985153763966752246839469)
          ·
            refine ⟨5244432661487532092564801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13985153763966752246839469 5244432661487532092564801)
            ·
              refine ⟨3933324496115649069423601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5244432661487532092564801 3933324496115649069423601)
              ·
                refine ⟨2949993372086736802067701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3933324496115649069423601 2949993372086736802067701)
                ·
                  refine ⟨276561878633131575193847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2949993372086736802067701 276561878633131575193847)
                  ·
                    rfl

theorem cell23_4847421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_4847421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847421 prefixEnd_4847421 := by exact prefixLift 4847421
  have htrace : WordTrace (prefixWord ++ tailWord_4847421) baseStart_4847421 baseEnd_4847421 := by
    simpa [prefixWord, tailWord_4847421, baseEnd_4847421] using wordTrace_append hprefix tailTrace_4847421
  have hstable : (prefixWord ++ tailWord_4847421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847421).length < 2 ^ (prefixWord ++ tailWord_4847421).sum := by decide
  have hdescent : baseEnd_4847421 < baseStart_4847421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847440 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 3]
def baseStart_4847440 : Nat := 118140960795 + 4847440 * 2 ^ 59
def prefixEnd_4847440 : Nat := 4983230072969 + 3 ^ 40 * 4847440 * 2
def baseEnd_4847440 : Nat := 2489066663830619602407035

theorem tailTrace_4847440 : CollatzResearch.WordTrace tailWord_4847440 prefixEnd_4847440 2489066663830619602407035 := by
  unfold tailWord_4847440
  simp only [CollatzResearch.WordTrace]
  refine ⟨88400330779280115843233887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117867107705706821124311849 88400330779280115843233887)
  ·
    refine ⟨132600496168920173764850831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88400330779280115843233887 132600496168920173764850831)
    ·
      refine ⟨198900744253380260647276247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132600496168920173764850831 198900744253380260647276247)
      ·
        refine ⟨298351116380070390970914371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198900744253380260647276247 298351116380070390970914371)
        ·
          refine ⟨447526674570105586456371557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298351116380070390970914371 447526674570105586456371557)
          ·
            refine ⟨83911251481894797460569667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 447526674570105586456371557 83911251481894797460569667)
            ·
              refine ⟨125866877222842196190854501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83911251481894797460569667 125866877222842196190854501)
              ·
                refine ⟨23600039479282911785785219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125866877222842196190854501 23600039479282911785785219)
                ·
                  refine ⟨35400059218924367678677829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23600039479282911785785219 35400059218924367678677829)
                  ·
                    refine ⟨6637511103548318939752093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35400059218924367678677829 6637511103548318939752093)
                    ·
                      refine ⟨2489066663830619602407035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6637511103548318939752093 2489066663830619602407035)
                      ·
                        rfl

theorem cell23_4847440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 3].length) (baseStart_4847440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847440 prefixEnd_4847440 := by exact prefixLift 4847440
  have htrace : WordTrace (prefixWord ++ tailWord_4847440) baseStart_4847440 baseEnd_4847440 := by
    simpa [prefixWord, tailWord_4847440, baseEnd_4847440] using wordTrace_append hprefix tailTrace_4847440
  have hstable : (prefixWord ++ tailWord_4847440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847440).length < 2 ^ (prefixWord ++ tailWord_4847440).sum := by decide
  have hdescent : baseEnd_4847440 < baseStart_4847440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847443 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 12]
def baseStart_4847443 : Nat := 118140960795 + 4847443 * 2 ^ 59
def prefixEnd_4847443 : Nat := 4983230072969 + 3 ^ 40 * 4847443 * 2
def baseEnd_4847443 : Nat := 276563133808064787852169

theorem tailTrace_4847443 : CollatzResearch.WordTrace tailWord_4847443 prefixEnd_4847443 276563133808064787852169 := by
  unfold tailWord_4847443
  simp only [CollatzResearch.WordTrace]
  refine ⟨176800770977549363198826983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117867180651699575465884655 176800770977549363198826983)
  ·
    refine ⟨265201156466324044798240475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176800770977549363198826983 265201156466324044798240475)
    ·
      refine ⟨397801734699486067197360713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265201156466324044798240475 397801734699486067197360713)
      ·
        refine ⟨298351301024614550398020535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397801734699486067197360713 298351301024614550398020535)
        ·
          refine ⟨447526951536921825597030803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298351301024614550398020535 447526951536921825597030803)
          ·
            refine ⟨671290427305382738395546205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447526951536921825597030803 671290427305382738395546205)
            ·
              refine ⟨251733910239518526898329827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 671290427305382738395546205 251733910239518526898329827)
              ·
                refine ⟨377600865359277790347494741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251733910239518526898329827 377600865359277790347494741)
                ·
                  refine ⟨276563133808064787852169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 377600865359277790347494741 276563133808064787852169)
                  ·
                    rfl

theorem cell23_4847443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 12].length) (baseStart_4847443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847443 prefixEnd_4847443 := by exact prefixLift 4847443
  have htrace : WordTrace (prefixWord ++ tailWord_4847443) baseStart_4847443 baseEnd_4847443 := by
    simpa [prefixWord, tailWord_4847443, baseEnd_4847443] using wordTrace_append hprefix tailTrace_4847443
  have hstable : (prefixWord ++ tailWord_4847443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847443).length < 2 ^ (prefixWord ++ tailWord_4847443).sum := by decide
  have hdescent : baseEnd_4847443 < baseStart_4847443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847497 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 3, 5, 2]
def baseStart_4847497 : Nat := 118140960795 + 4847497 * 2 ^ 59
def prefixEnd_4847497 : Nat := 4983230072969 + 3 ^ 40 * 4847497 * 2
def baseEnd_4847497 : Nat := 2489095932227925879394273

theorem tailTrace_4847497 : CollatzResearch.WordTrace tailWord_4847497 prefixEnd_4847497 2489095932227925879394273 := by
  unfold tailWord_4847497
  simp only [CollatzResearch.WordTrace]
  refine ⟨176802740519353730421292745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117868493679569153614195163 176802740519353730421292745)
  ·
    refine ⟨132602055389515297815969559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176802740519353730421292745 132602055389515297815969559)
    ·
      refine ⟨198903083084272946723954339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132602055389515297815969559 198903083084272946723954339)
      ·
        refine ⟨298354624626409420085931509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198903083084272946723954339 298354624626409420085931509)
        ·
          refine ⟨27970746058725883133056079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 298354624626409420085931509 27970746058725883133056079)
          ·
            refine ⟨41956119088088824699584119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27970746058725883133056079 41956119088088824699584119)
            ·
              refine ⟨62934178632133237049376179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41956119088088824699584119 62934178632133237049376179)
              ·
                refine ⟨94401267948199855574064269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62934178632133237049376179 94401267948199855574064269)
                ·
                  refine ⟨35400475480574945840274101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94401267948199855574064269 35400475480574945840274101)
                  ·
                    refine ⟨3318794576303901172525697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35400475480574945840274101 3318794576303901172525697)
                    ·
                      refine ⟨2489095932227925879394273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3318794576303901172525697 2489095932227925879394273)
                      ·
                        rfl

theorem cell23_4847497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 5, 2].length) (baseStart_4847497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847497 prefixEnd_4847497 := by exact prefixLift 4847497
  have htrace : WordTrace (prefixWord ++ tailWord_4847497) baseStart_4847497 baseEnd_4847497 := by
    simpa [prefixWord, tailWord_4847497, baseEnd_4847497] using wordTrace_append hprefix tailTrace_4847497
  have hstable : (prefixWord ++ tailWord_4847497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847497).length < 2 ^ (prefixWord ++ tailWord_4847497).sum := by decide
  have hdescent : baseEnd_4847497 < baseStart_4847497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847514 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2]
def baseStart_4847514 : Nat := 118140960795 + 4847514 * 2 ^ 59
def prefixEnd_4847514 : Nat := 4983230072969 + 3 ^ 40 * 4847514 * 2
def baseEnd_4847514 : Nat := 2489104661399052312881695

theorem tailTrace_4847514 : CollatzResearch.WordTrace tailWord_4847514 prefixEnd_4847514 2489104661399052312881695 := by
  unfold tailWord_4847514
  simp only [CollatzResearch.WordTrace]
  refine ⟨44200840140073035581165399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117868907040194761549774397 44200840140073035581165399)
  ·
    refine ⟨66301260210109553371748099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44200840140073035581165399 66301260210109553371748099)
    ·
      refine ⟨99451890315164330057622149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66301260210109553371748099 99451890315164330057622149)
      ·
        refine ⟨18647229434093311885804153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99451890315164330057622149 18647229434093311885804153)
        ·
          refine ⟨13985422075569983914353115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18647229434093311885804153 13985422075569983914353115)
          ·
            refine ⟨20978133113354975871529673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13985422075569983914353115 20978133113354975871529673)
            ·
              refine ⟨15733599835016231903647255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20978133113354975871529673 15733599835016231903647255)
              ·
                refine ⟨23600399752524347855470883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15733599835016231903647255 23600399752524347855470883)
                ·
                  refine ⟨35400599628786521783206325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23600399752524347855470883 35400599628786521783206325)
                  ·
                    refine ⟨3318806215198736417175593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35400599628786521783206325 3318806215198736417175593)
                    ·
                      refine ⟨2489104661399052312881695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3318806215198736417175593 2489104661399052312881695)
                      ·
                        rfl

theorem cell23_4847514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_4847514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847514 prefixEnd_4847514 := by exact prefixLift 4847514
  have htrace : WordTrace (prefixWord ++ tailWord_4847514) baseStart_4847514 baseEnd_4847514 := by
    simpa [prefixWord, tailWord_4847514, baseEnd_4847514] using wordTrace_append hprefix tailTrace_4847514
  have hstable : (prefixWord ++ tailWord_4847514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847514).length < 2 ^ (prefixWord ++ tailWord_4847514).sum := by decide
  have hdescent : baseEnd_4847514 < baseStart_4847514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847520 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 3, 6]
def baseStart_4847520 : Nat := 118140960795 + 4847520 * 2 ^ 59
def prefixEnd_4847520 : Nat := 4983230072969 + 3 ^ 40 * 4847520 * 2
def baseEnd_4847520 : Nat := 829702580760993096468889

theorem tailTrace_4847520 : CollatzResearch.WordTrace tailWord_4847520 prefixEnd_4847520 829702580760993096468889 := by
  unfold tailWord_4847520
  simp only [CollatzResearch.WordTrace]
  refine ⟨88401789699135202674690007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117869052932180270232920009 88401789699135202674690007)
  ·
    refine ⟨132602684548702804012035011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88401789699135202674690007 132602684548702804012035011)
    ·
      refine ⟨198904026823054206018052517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132602684548702804012035011 198904026823054206018052517)
      ·
        refine ⟨37294505029322663628384847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198904026823054206018052517 37294505029322663628384847)
        ·
          refine ⟨55941757543983995442577271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37294505029322663628384847 55941757543983995442577271)
          ·
            refine ⟨83912636315975993163865907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55941757543983995442577271 83912636315975993163865907)
            ·
              refine ⟨125868954473963989745798861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83912636315975993163865907 125868954473963989745798861)
              ·
                refine ⟨47200857927736496154674573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125868954473963989745798861 47200857927736496154674573)
                ·
                  refine ⟨17700321722901186058002965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47200857927736496154674573 17700321722901186058002965)
                  ·
                    refine ⟨829702580760993096468889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17700321722901186058002965 829702580760993096468889)
                    ·
                      rfl

theorem cell23_4847520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_4847520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847520 prefixEnd_4847520 := by exact prefixLift 4847520
  have htrace : WordTrace (prefixWord ++ tailWord_4847520) baseStart_4847520 baseEnd_4847520 := by
    simpa [prefixWord, tailWord_4847520, baseEnd_4847520] using wordTrace_append hprefix tailTrace_4847520
  have hstable : (prefixWord ++ tailWord_4847520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847520).length < 2 ^ (prefixWord ++ tailWord_4847520).sum := by decide
  have hdescent : baseEnd_4847520 < baseStart_4847520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847564 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 3, 2, 3]
def baseStart_4847564 : Nat := 118140960795 + 4847564 * 2 ^ 59
def prefixEnd_4847564 : Nat := 4983230072969 + 3 ^ 40 * 4847564 * 2
def baseEnd_4847564 : Nat := 2489130335431777117256465

theorem tailTrace_4847564 : CollatzResearch.WordTrace tailWord_4847564 prefixEnd_4847564 2489130335431777117256465 := by
  unfold tailWord_4847564
  simp only [CollatzResearch.WordTrace]
  refine ⟨88402592105055500431990873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117870122806740667242654497 88402592105055500431990873)
  ·
    refine ⟨66301944078791625323993155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88402592105055500431990873 66301944078791625323993155)
    ·
      refine ⟨99452916118187437985989733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66301944078791625323993155 99452916118187437985989733)
      ·
        refine ⟨18647421772160144622373075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99452916118187437985989733 18647421772160144622373075)
        ·
          refine ⟨27971132658240216933559613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18647421772160144622373075 27971132658240216933559613)
          ·
            refine ⟨10489174746840081350084855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27971132658240216933559613 10489174746840081350084855)
            ·
              refine ⟨15733762120260122025127283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10489174746840081350084855 15733762120260122025127283)
              ·
                refine ⟨23600643180390183037690925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15733762120260122025127283 23600643180390183037690925)
                ·
                  refine ⟨8850241192646318639134097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23600643180390183037690925 8850241192646318639134097)
                  ·
                    refine ⟨6637680894484738979350573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8850241192646318639134097 6637680894484738979350573)
                    ·
                      refine ⟨2489130335431777117256465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6637680894484738979350573 2489130335431777117256465)
                      ·
                        rfl

theorem cell23_4847564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_4847564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847564 prefixEnd_4847564 := by exact prefixLift 4847564
  have htrace : WordTrace (prefixWord ++ tailWord_4847564) baseStart_4847564 baseEnd_4847564 := by
    simpa [prefixWord, tailWord_4847564, baseEnd_4847564] using wordTrace_append hprefix tailTrace_4847564
  have hstable : (prefixWord ++ tailWord_4847564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847564).length < 2 ^ (prefixWord ++ tailWord_4847564).sum := by decide
  have hdescent : baseEnd_4847564 < baseStart_4847564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847581 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_4847581 : Nat := 118140960795 + 4847581 * 2 ^ 59
def prefixEnd_4847581 : Nat := 4983230072969 + 3 ^ 40 * 4847581 * 2
def baseEnd_4847581 : Nat := 2489139064602903550743887

theorem tailTrace_4847581 : CollatzResearch.WordTrace tailWord_4847581 prefixEnd_4847581 2489139064602903550743887 := by
  unfold tailWord_4847581
  simp only [CollatzResearch.WordTrace]
  refine ⟨176805804251049412767350597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117870536167366275178233731 176805804251049412767350597)
  ·
    refine ⟨33151088297071764893878237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176805804251049412767350597 33151088297071764893878237)
    ·
      refine ⟨12431658111401911835204339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33151088297071764893878237 12431658111401911835204339)
      ·
        refine ⟨18647487167102867752806509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12431658111401911835204339 18647487167102867752806509)
        ·
          refine ⟨6992807687663575407302441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18647487167102867752806509 6992807687663575407302441)
          ·
            refine ⟨5244605765747681555476831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6992807687663575407302441 5244605765747681555476831)
            ·
              refine ⟨7866908648621522333215247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5244605765747681555476831 7866908648621522333215247)
              ·
                refine ⟨11800362972932283499822871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7866908648621522333215247 11800362972932283499822871)
                ·
                  refine ⟨17700544459398425249734307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11800362972932283499822871 17700544459398425249734307)
                  ·
                    refine ⟨26550816689097637874601461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17700544459398425249734307 26550816689097637874601461)
                    ·
                      refine ⟨2489139064602903550743887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26550816689097637874601461 2489139064602903550743887)
                      ·
                        rfl

theorem cell23_4847581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_4847581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847581 prefixEnd_4847581 := by exact prefixLift 4847581
  have htrace : WordTrace (prefixWord ++ tailWord_4847581) baseStart_4847581 baseEnd_4847581 := by
    simpa [prefixWord, tailWord_4847581, baseEnd_4847581] using wordTrace_append hprefix tailTrace_4847581
  have hstable : (prefixWord ++ tailWord_4847581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847581).length < 2 ^ (prefixWord ++ tailWord_4847581).sum := by decide
  have hdescent : baseEnd_4847581 < baseStart_4847581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847617 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_4847617 : Nat := 118140960795 + 4847617 * 2 ^ 59
def prefixEnd_4847617 : Nat := 4983230072969 + 3 ^ 40 * 4847617 * 2
def baseEnd_4847617 : Nat := 2489157549906465409893721

theorem tailTrace_4847617 : CollatzResearch.WordTrace tailWord_4847617 prefixEnd_4847617 2489157549906465409893721 := by
  unfold tailWord_4847617
  simp only [CollatzResearch.WordTrace]
  refine ⟨176807117278918990915661105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117871411519279327277107403 176807117278918990915661105)
  ·
    refine ⟨132605337959189243186745829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176807117278918990915661105 132605337959189243186745829)
    ·
      refine ⟨24863500867347983097514843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132605337959189243186745829 24863500867347983097514843)
      ·
        refine ⟨37295251301021974646272265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24863500867347983097514843 37295251301021974646272265)
        ·
          refine ⟨27971438475766480984704199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37295251301021974646272265 27971438475766480984704199)
          ·
            refine ⟨41957157713649721477056299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27971438475766480984704199 41957157713649721477056299)
            ·
              refine ⟨62935736570474582215584449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41957157713649721477056299 62935736570474582215584449)
              ·
                refine ⟨47201802427855936661688337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62935736570474582215584449 47201802427855936661688337)
                ·
                  refine ⟨35401351820891952496266253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47201802427855936661688337 35401351820891952496266253)
                  ·
                    refine ⟨13275506932834482186099845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35401351820891952496266253 13275506932834482186099845)
                    ·
                      refine ⟨2489157549906465409893721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13275506932834482186099845 2489157549906465409893721)
                      ·
                        rfl

theorem cell23_4847617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_4847617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847617 prefixEnd_4847617 := by exact prefixLift 4847617
  have htrace : WordTrace (prefixWord ++ tailWord_4847617) baseStart_4847617 baseEnd_4847617 := by
    simpa [prefixWord, tailWord_4847617, baseEnd_4847617] using wordTrace_append hprefix tailTrace_4847617
  have hstable : (prefixWord ++ tailWord_4847617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847617).length < 2 ^ (prefixWord ++ tailWord_4847617).sum := by decide
  have hdescent : baseEnd_4847617 < baseStart_4847617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847629 : List Nat := [1, 7, 1, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_4847629 : Nat := 118140960795 + 4847629 * 2 ^ 59
def prefixEnd_4847629 : Nat := 4983230072969 + 3 ^ 40 * 4847629 * 2
def baseEnd_4847629 : Nat := 2489163711674319362943667

theorem tailTrace_4847629 : CollatzResearch.WordTrace tailWord_4847629 prefixEnd_4847629 2489163711674319362943667 := by
  unfold tailWord_4847629
  simp only [CollatzResearch.WordTrace]
  refine ⟨176807554954875516965097941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117871703303250344643398627 176807554954875516965097941)
  ·
    refine ⟨4143927069254894928869483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 176807554954875516965097941 4143927069254894928869483)
    ·
      refine ⟨6215890603882342393304225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4143927069254894928869483 6215890603882342393304225)
      ·
        refine ⟨4661917952911756794978169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6215890603882342393304225 4661917952911756794978169)
        ·
          refine ⟨3496438464683817596233627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4661917952911756794978169 3496438464683817596233627)
          ·
            refine ⟨5244657697025726394350441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3496438464683817596233627 5244657697025726394350441)
            ·
              refine ⟨3933493272769294795762831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5244657697025726394350441 3933493272769294795762831)
              ·
                refine ⟨5900239909153942193644247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933493272769294795762831 5900239909153942193644247)
                ·
                  refine ⟨8850359863730913290466371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5900239909153942193644247 8850359863730913290466371)
                  ·
                    refine ⟨13275539795596369935699557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8850359863730913290466371 13275539795596369935699557)
                    ·
                      refine ⟨2489163711674319362943667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13275539795596369935699557 2489163711674319362943667)
                      ·
                        rfl

theorem cell23_4847629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_4847629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847629 prefixEnd_4847629 := by exact prefixLift 4847629
  have htrace : WordTrace (prefixWord ++ tailWord_4847629) baseStart_4847629 baseEnd_4847629 := by
    simpa [prefixWord, tailWord_4847629, baseEnd_4847629] using wordTrace_append hprefix tailTrace_4847629
  have hstable : (prefixWord ++ tailWord_4847629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847629).length < 2 ^ (prefixWord ++ tailWord_4847629).sum := by decide
  have hdescent : baseEnd_4847629 < baseStart_4847629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847647 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 4]
def baseStart_4847647 : Nat := 118140960795 + 4847647 * 2 ^ 59
def prefixEnd_4847647 : Nat := 4983230072969 + 3 ^ 40 * 4847647 * 2
def baseEnd_4847647 : Nat := 2489172954326100292518583

theorem tailTrace_4847647 : CollatzResearch.WordTrace tailWord_4847647 prefixEnd_4847647 2489172954326100292518583 := by
  unfold tailWord_4847647
  simp only [CollatzResearch.WordTrace]
  refine ⟨176808211468810306039253195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117872140979206870692835463 176808211468810306039253195)
  ·
    refine ⟨265212317203215459058879793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176808211468810306039253195 265212317203215459058879793)
    ·
      refine ⟨198909237902411594294159845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265212317203215459058879793 198909237902411594294159845)
      ·
        refine ⟨37295482106702173930154971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198909237902411594294159845 37295482106702173930154971)
        ·
          refine ⟨55943223160053260895232457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37295482106702173930154971 55943223160053260895232457)
          ·
            refine ⟨41957417370039945671424343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55943223160053260895232457 41957417370039945671424343)
            ·
              refine ⟨62936126055059918507136515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41957417370039945671424343 62936126055059918507136515)
              ·
                refine ⟨94404189082589877760704773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62936126055059918507136515 94404189082589877760704773)
                ·
                  refine ⟨17700785452985602080132145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94404189082589877760704773 17700785452985602080132145)
                  ·
                    refine ⟨13275589089739201560099109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17700785452985602080132145 13275589089739201560099109)
                    ·
                      refine ⟨2489172954326100292518583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13275589089739201560099109 2489172954326100292518583)
                      ·
                        rfl

theorem cell23_4847647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_4847647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847647 prefixEnd_4847647 := by exact prefixLift 4847647
  have htrace : WordTrace (prefixWord ++ tailWord_4847647) baseStart_4847647 baseEnd_4847647 := by
    simpa [prefixWord, tailWord_4847647, baseEnd_4847647] using wordTrace_append hprefix tailTrace_4847647
  have hstable : (prefixWord ++ tailWord_4847647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847647).length < 2 ^ (prefixWord ++ tailWord_4847647).sum := by decide
  have hdescent : baseEnd_4847647 < baseStart_4847647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847651 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 4, 2, 2]
def baseStart_4847651 : Nat := 118140960795 + 4847651 * 2 ^ 59
def prefixEnd_4847651 : Nat := 4983230072969 + 3 ^ 40 * 4847651 * 2
def baseEnd_4847651 : Nat := 2489175008248718276868565

theorem tailTrace_4847651 : CollatzResearch.WordTrace tailWord_4847651 prefixEnd_4847651 2489175008248718276868565 := by
  unfold tailWord_4847651
  simp only [CollatzResearch.WordTrace]
  refine ⟨176808357360795814722398807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117872238240530543148265871 176808357360795814722398807)
  ·
    refine ⟨265212536041193722083598211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176808357360795814722398807 265212536041193722083598211)
    ·
      refine ⟨397818804061790583125397317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265212536041193722083598211 397818804061790583125397317)
      ·
        refine ⟨74591025761585734336011997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 397818804061790583125397317 74591025761585734336011997)
        ·
          refine ⟨27971634660594650376004499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74591025761585734336011997 27971634660594650376004499)
          ·
            refine ⟨41957451990891975564006749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27971634660594650376004499 41957451990891975564006749)
            ·
              refine ⟨15734044496584490836502531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41957451990891975564006749 15734044496584490836502531)
              ·
                refine ⟨23601066744876736254753797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15734044496584490836502531 23601066744876736254753797)
                ·
                  refine ⟨4425200014664388047766337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23601066744876736254753797 4425200014664388047766337)
                  ·
                    refine ⟨3318900010998291035824753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4425200014664388047766337 3318900010998291035824753)
                    ·
                      refine ⟨2489175008248718276868565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3318900010998291035824753 2489175008248718276868565)
                      ·
                        rfl

theorem cell23_4847651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_4847651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847651 prefixEnd_4847651 := by exact prefixLift 4847651
  have htrace : WordTrace (prefixWord ++ tailWord_4847651) baseStart_4847651 baseEnd_4847651 := by
    simpa [prefixWord, tailWord_4847651, baseEnd_4847651] using wordTrace_append hprefix tailTrace_4847651
  have hstable : (prefixWord ++ tailWord_4847651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847651).length < 2 ^ (prefixWord ++ tailWord_4847651).sum := by decide
  have hdescent : baseEnd_4847651 < baseStart_4847651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847687 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 1, 7]
def baseStart_4847687 : Nat := 118140960795 + 4847687 * 2 ^ 59
def prefixEnd_4847687 : Nat := 4983230072969 + 3 ^ 40 * 4847687 * 2
def baseEnd_4847687 : Nat := 829731164517426712006133

theorem tailTrace_4847687 : CollatzResearch.WordTrace tailWord_4847687 prefixEnd_4847687 829731164517426712006133 := by
  unfold tailWord_4847687
  simp only [CollatzResearch.WordTrace]
  refine ⟨176809670388665392870709315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117873113592443595247139543 176809670388665392870709315)
  ·
    refine ⟨265214505582998089306063973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176809670388665392870709315 265214505582998089306063973)
    ·
      refine ⟨49727719796812141744886995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265214505582998089306063973 49727719796812141744886995)
      ·
        refine ⟨74591579695218212617330493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49727719796812141744886995 74591579695218212617330493)
        ·
          refine ⟨27971842385706829731498935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74591579695218212617330493 27971842385706829731498935)
          ·
            refine ⟨41957763578560244597248403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27971842385706829731498935 41957763578560244597248403)
            ·
              refine ⟨62936645367840366895872605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41957763578560244597248403 62936645367840366895872605)
              ·
                refine ⟨23601242012940137585952227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62936645367840366895872605 23601242012940137585952227)
                ·
                  refine ⟨35401863019410206378928341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23601242012940137585952227 35401863019410206378928341)
                  ·
                    refine ⟨829731164517426712006133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35401863019410206378928341 829731164517426712006133)
                    ·
                      rfl

theorem cell23_4847687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_4847687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847687 prefixEnd_4847687 := by exact prefixLift 4847687
  have htrace : WordTrace (prefixWord ++ tailWord_4847687) baseStart_4847687 baseEnd_4847687 := by
    simpa [prefixWord, tailWord_4847687, baseEnd_4847687] using wordTrace_append hprefix tailTrace_4847687
  have hstable : (prefixWord ++ tailWord_4847687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847687).length < 2 ^ (prefixWord ++ tailWord_4847687).sum := by decide
  have hdescent : baseEnd_4847687 < baseStart_4847687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847697 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_4847697 : Nat := 118140960795 + 4847697 * 2 ^ 59
def prefixEnd_4847697 : Nat := 4983230072969 + 3 ^ 40 * 4847697 * 2
def baseEnd_4847697 : Nat := 2489198628358825096893353

theorem tailTrace_4847697 : CollatzResearch.WordTrace tailWord_4847697 prefixEnd_4847697 2489198628358825096893353 := by
  unfold tailWord_4847697
  simp only [CollatzResearch.WordTrace]
  refine ⟨176810035118629164578573345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117873356745752776385715563 176810035118629164578573345)
  ·
    refine ⟨132607526338971873433930009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176810035118629164578573345 132607526338971873433930009)
    ·
      refine ⟨99455644754228905075447507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132607526338971873433930009 99455644754228905075447507)
      ·
        refine ⟨149183467131343357613171261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99455644754228905075447507 149183467131343357613171261)
        ·
          refine ⟨55943800174253759104939223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149183467131343357613171261 55943800174253759104939223)
          ·
            refine ⟨83915700261380638657408835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55943800174253759104939223 83915700261380638657408835)
            ·
              refine ⟨125873550392070957986113253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83915700261380638657408835 125873550392070957986113253)
              ·
                refine ⟨23601290698513304622396235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125873550392070957986113253 23601290698513304622396235)
                ·
                  refine ⟨35401936047769956933594353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23601290698513304622396235 35401936047769956933594353)
                  ·
                    refine ⟨26551452035827467700195765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35401936047769956933594353 26551452035827467700195765)
                    ·
                      refine ⟨2489198628358825096893353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26551452035827467700195765 2489198628358825096893353)
                      ·
                        rfl

theorem cell23_4847697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_4847697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847697 prefixEnd_4847697 := by exact prefixLift 4847697
  have htrace : WordTrace (prefixWord ++ tailWord_4847697) baseStart_4847697 baseEnd_4847697 := by
    simpa [prefixWord, tailWord_4847697, baseEnd_4847697] using wordTrace_append hprefix tailTrace_4847697
  have hstable : (prefixWord ++ tailWord_4847697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847697).length < 2 ^ (prefixWord ++ tailWord_4847697).sum := by decide
  have hdescent : baseEnd_4847697 < baseStart_4847697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847704 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 2, 5]
def baseStart_4847704 : Nat := 118140960795 + 4847704 * 2 ^ 59
def prefixEnd_4847704 : Nat := 4983230072969 + 3 ^ 40 * 4847704 * 2
def baseEnd_4847704 : Nat := 829734074241135523168607

theorem tailTrace_4847704 : CollatzResearch.WordTrace tailWord_4847704 prefixEnd_4847704 829734074241135523168607 := by
  unfold tailWord_4847704
  simp only [CollatzResearch.WordTrace]
  refine ⟨88405145214801902387039083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117873526953069203182718777 88405145214801902387039083)
  ·
    refine ⟨132607717822202853580558625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88405145214801902387039083 132607717822202853580558625)
    ·
      refine ⟨99455788366652140185418969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132607717822202853580558625 99455788366652140185418969)
      ·
        refine ⟨74591841274989105139064227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99455788366652140185418969 74591841274989105139064227)
        ·
          refine ⟨111887761912483657708596341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74591841274989105139064227 111887761912483657708596341)
          ·
            refine ⟨10489477679295342910180907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111887761912483657708596341 10489477679295342910180907)
            ·
              refine ⟨15734216518943014365271361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10489477679295342910180907 15734216518943014365271361)
              ·
                refine ⟨11800662389207260773953521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15734216518943014365271361 11800662389207260773953521)
                ·
                  refine ⟨8850496791905445580465141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11800662389207260773953521 8850496791905445580465141)
                  ·
                    refine ⟨829734074241135523168607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8850496791905445580465141 829734074241135523168607)
                    ·
                      rfl

theorem cell23_4847704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_4847704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847704 prefixEnd_4847704 := by exact prefixLift 4847704
  have htrace : WordTrace (prefixWord ++ tailWord_4847704) baseStart_4847704 baseEnd_4847704 := by
    simpa [prefixWord, tailWord_4847704, baseEnd_4847704] using wordTrace_append hprefix tailTrace_4847704
  have hstable : (prefixWord ++ tailWord_4847704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847704).length < 2 ^ (prefixWord ++ tailWord_4847704).sum := by decide
  have hdescent : baseEnd_4847704 < baseStart_4847704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847708 : List Nat := [2, 2, 4, 1, 1, 3, 3, 2, 5]
def baseStart_4847708 : Nat := 118140960795 + 4847708 * 2 ^ 59
def prefixEnd_4847708 : Nat := 4983230072969 + 3 ^ 40 * 4847708 * 2
def baseEnd_4847708 : Nat := 276578252960669394872867

theorem tailTrace_4847708 : CollatzResearch.WordTrace tailWord_4847708 prefixEnd_4847708 276578252960669394872867 := by
  unfold tailWord_4847708
  simp only [CollatzResearch.WordTrace]
  refine ⟨88405218160794656728611889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117873624214392875638149185 88405218160794656728611889)
  ·
    refine ⟨66303913620595992546458917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88405218160794656728611889 66303913620595992546458917)
    ·
      refine ⟨12431983803861748602461047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66303913620595992546458917 12431983803861748602461047)
      ·
        refine ⟨18647975705792622903691571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12431983803861748602461047 18647975705792622903691571)
        ·
          refine ⟨27971963558688934355537357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18647975705792622903691571 27971963558688934355537357)
          ·
            refine ⟨10489486334508350383326509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27971963558688934355537357 10489486334508350383326509)
            ·
              refine ⟨3933557375440631393747441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10489486334508350383326509 3933557375440631393747441)
              ·
                refine ⟨2950168031580473545310581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3933557375440631393747441 2950168031580473545310581)
                ·
                  refine ⟨276578252960669394872867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2950168031580473545310581 276578252960669394872867)
                  ·
                    rfl

theorem cell23_4847708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 2, 5].length) (baseStart_4847708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847708 prefixEnd_4847708 := by exact prefixLift 4847708
  have htrace : WordTrace (prefixWord ++ tailWord_4847708) baseStart_4847708 baseEnd_4847708 := by
    simpa [prefixWord, tailWord_4847708, baseEnd_4847708] using wordTrace_append hprefix tailTrace_4847708
  have hstable : (prefixWord ++ tailWord_4847708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847708).length < 2 ^ (prefixWord ++ tailWord_4847708).sum := by decide
  have hdescent : baseEnd_4847708 < baseStart_4847708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847741 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_4847741 : Nat := 118140960795 + 4847741 * 2 ^ 59
def prefixEnd_4847741 : Nat := 4983230072969 + 3 ^ 40 * 4847741 * 2
def baseEnd_4847741 : Nat := 2489221221507622924743151

theorem tailTrace_4847741 : CollatzResearch.WordTrace tailWord_4847741 prefixEnd_4847741 2489221221507622924743151 := by
  unfold tailWord_4847741
  simp only [CollatzResearch.WordTrace]
  refine ⟨176811639930469760093175077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117874426620313173395450051 176811639930469760093175077)
  ·
    refine ⟨33152182486963080017470327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176811639930469760093175077 33152182486963080017470327)
    ·
      refine ⟨49728273730444620026205491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33152182486963080017470327 49728273730444620026205491)
      ·
        refine ⟨74592410595666930039308237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49728273730444620026205491 74592410595666930039308237)
        ·
          refine ⟨27972153973375098764740589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74592410595666930039308237 27972153973375098764740589)
          ·
            refine ⟨10489557740015662036777721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27972153973375098764740589 10489557740015662036777721)
            ·
              refine ⟨7867168305011746527583291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10489557740015662036777721 7867168305011746527583291)
              ·
                refine ⟨11800752457517619791374937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7867168305011746527583291 11800752457517619791374937)
                ·
                  refine ⟨8850564343138214843531203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11800752457517619791374937 8850564343138214843531203)
                  ·
                    refine ⟨13275846514707322265296805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8850564343138214843531203 13275846514707322265296805)
                    ·
                      refine ⟨2489221221507622924743151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13275846514707322265296805 2489221221507622924743151)
                      ·
                        rfl

theorem cell23_4847741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_4847741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847741 prefixEnd_4847741 := by exact prefixLift 4847741
  have htrace : WordTrace (prefixWord ++ tailWord_4847741) baseStart_4847741 baseEnd_4847741 := by
    simpa [prefixWord, tailWord_4847741, baseEnd_4847741] using wordTrace_append hprefix tailTrace_4847741
  have hstable : (prefixWord ++ tailWord_4847741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847741).length < 2 ^ (prefixWord ++ tailWord_4847741).sum := by decide
  have hdescent : baseEnd_4847741 < baseStart_4847741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847787 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 5]
def baseStart_4847787 : Nat := 118140960795 + 4847787 * 2 ^ 59
def prefixEnd_4847787 : Nat := 4983230072969 + 3 ^ 40 * 4847787 * 2
def baseEnd_4847787 : Nat := 2489244841617729744767939

theorem tailTrace_4847787 : CollatzResearch.WordTrace tailWord_4847787 prefixEnd_4847787 2489244841617729744767939 := by
  unfold tailWord_4847787
  simp only [CollatzResearch.WordTrace]
  refine ⟨176813317688303109949349615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117875545125535406632899743 176813317688303109949349615)
  ·
    refine ⟨265219976532454664924024423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176813317688303109949349615 265219976532454664924024423)
    ·
      refine ⟨397829964798681997386036635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265219976532454664924024423 397829964798681997386036635)
      ·
        refine ⟨596744947198022996079054953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397829964798681997386036635 596744947198022996079054953)
        ·
          refine ⟨447558710398517247059291215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 596744947198022996079054953 447558710398517247059291215)
          ·
            refine ⟨671338065597775870588936823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447558710398517247059291215 671338065597775870588936823)
            ·
              refine ⟨1007007098396663805883405235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671338065597775870588936823 1007007098396663805883405235)
              ·
                refine ⟨1510510647594995708825107853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007007098396663805883405235 1510510647594995708825107853)
                ·
                  refine ⟨566441492848123390809415445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1510510647594995708825107853 566441492848123390809415445)
                  ·
                    refine ⟨26551944977255783944191349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 566441492848123390809415445 26551944977255783944191349)
                    ·
                      refine ⟨2489244841617729744767939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26551944977255783944191349 2489244841617729744767939)
                      ·
                        rfl

theorem cell23_4847787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 5].length) (baseStart_4847787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847787 prefixEnd_4847787 := by exact prefixLift 4847787
  have htrace : WordTrace (prefixWord ++ tailWord_4847787) baseStart_4847787 baseEnd_4847787 := by
    simpa [prefixWord, tailWord_4847787, baseEnd_4847787] using wordTrace_append hprefix tailTrace_4847787
  have hstable : (prefixWord ++ tailWord_4847787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847787).length < 2 ^ (prefixWord ++ tailWord_4847787).sum := by decide
  have hdescent : baseEnd_4847787 < baseStart_4847787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847794 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_4847794 : Nat := 118140960795 + 4847794 * 2 ^ 59
def prefixEnd_4847794 : Nat := 4983230072969 + 3 ^ 40 * 4847794 * 2
def baseEnd_4847794 : Nat := 829749478660770405793469

theorem tailTrace_4847794 : CollatzResearch.WordTrace tailWord_4847794 prefixEnd_4847794 829749478660770405793469 := by
  unfold tailWord_4847794
  simp only [CollatzResearch.WordTrace]
  refine ⟨44203393249819437536213609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117875715332851833429902957 44203393249819437536213609)
  ·
    refine ⟨33152544937364578152160207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44203393249819437536213609 33152544937364578152160207)
    ·
      refine ⟨49728817406046867228240311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33152544937364578152160207 49728817406046867228240311)
      ·
        refine ⟨74593226109070300842360467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49728817406046867228240311 74593226109070300842360467)
        ·
          refine ⟨111889839163605451263540701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74593226109070300842360467 111889839163605451263540701)
          ·
            refine ⟨41958689686352044223827763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111889839163605451263540701 41958689686352044223827763)
            ·
              refine ⟨62938034529528066335741645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41958689686352044223827763 62938034529528066335741645)
              ·
                refine ⟨23601762948573024875903117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62938034529528066335741645 23601762948573024875903117)
                ·
                  refine ⟨8850661105714884328463669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23601762948573024875903117 8850661105714884328463669)
                  ·
                    refine ⟨829749478660770405793469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8850661105714884328463669 829749478660770405793469)
                    ·
                      rfl

theorem cell23_4847794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_4847794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847794 prefixEnd_4847794 := by exact prefixLift 4847794
  have htrace : WordTrace (prefixWord ++ tailWord_4847794) baseStart_4847794 baseEnd_4847794 := by
    simpa [prefixWord, tailWord_4847794, baseEnd_4847794] using wordTrace_append hprefix tailTrace_4847794
  have hstable : (prefixWord ++ tailWord_4847794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847794).length < 2 ^ (prefixWord ++ tailWord_4847794).sum := by decide
  have hdescent : baseEnd_4847794 < baseStart_4847794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847801 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 1, 5, 2]
def baseStart_4847801 : Nat := 118140960795 + 4847801 * 2 ^ 59
def prefixEnd_4847801 : Nat := 4983230072969 + 3 ^ 40 * 4847801 * 2
def baseEnd_4847801 : Nat := 2489252030346892689992875

theorem tailTrace_4847801 : CollatzResearch.WordTrace tailWord_4847801 prefixEnd_4847801 2489252030346892689992875 := by
  unfold tailWord_4847801
  simp only [CollatzResearch.WordTrace]
  refine ⟨176813828310252390340359257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117875885540168260226906171 176813828310252390340359257)
  ·
    refine ⟨132610371232689292755269443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176813828310252390340359257 132610371232689292755269443)
    ·
      refine ⟨198915556849033939132904165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132610371232689292755269443 198915556849033939132904165)
      ·
        refine ⟨37296666909193863587419531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198915556849033939132904165 37296666909193863587419531)
        ·
          refine ⟨55945000363790795381129297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37296666909193863587419531 55945000363790795381129297)
          ·
            refine ⟨41958750272843096535846973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55945000363790795381129297 41958750272843096535846973)
            ·
              refine ⟨15734531352316161200942615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41958750272843096535846973 15734531352316161200942615)
              ·
                refine ⟨23601797028474241801413923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15734531352316161200942615 23601797028474241801413923)
                ·
                  refine ⟨35402695542711362702120885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23601797028474241801413923 35402695542711362702120885)
                  ·
                    refine ⟨3319002707129190253323833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35402695542711362702120885 3319002707129190253323833)
                    ·
                      refine ⟨2489252030346892689992875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3319002707129190253323833 2489252030346892689992875)
                      ·
                        rfl

theorem cell23_4847801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_4847801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847801 prefixEnd_4847801 := by exact prefixLift 4847801
  have htrace : WordTrace (prefixWord ++ tailWord_4847801) baseStart_4847801 baseEnd_4847801 := by
    simpa [prefixWord, tailWord_4847801, baseEnd_4847801] using wordTrace_append hprefix tailTrace_4847801
  have hstable : (prefixWord ++ tailWord_4847801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847801).length < 2 ^ (prefixWord ++ tailWord_4847801).sum := by decide
  have hdescent : baseEnd_4847801 < baseStart_4847801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847834 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_4847834 : Nat := 118140960795 + 4847834 * 2 ^ 59
def prefixEnd_4847834 : Nat := 4983230072969 + 3 ^ 40 * 4847834 * 2
def baseEnd_4847834 : Nat := 2489268975208491060880223

theorem tailTrace_4847834 : CollatzResearch.WordTrace tailWord_4847834 prefixEnd_4847834 2489268975208491060880223 := by
  unfold tailWord_4847834
  simp only [CollatzResearch.WordTrace]
  refine ⟨44203757979783209244077639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117876687946088557984207037 44203757979783209244077639)
  ·
    refine ⟨66305636969674813866116459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44203757979783209244077639 66305636969674813866116459)
    ·
      refine ⟨99458455454512220799174689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66305636969674813866116459 99458455454512220799174689)
      ·
        refine ⟨74593841590884165599381017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99458455454512220799174689 74593841590884165599381017)
        ·
          refine ⟨55945381193163124199535763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74593841590884165599381017 55945381193163124199535763)
          ·
            refine ⟨83918071789744686299303645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55945381193163124199535763 83918071789744686299303645)
            ·
              refine ⟨31469276921154257362238867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83918071789744686299303645 31469276921154257362238867)
              ·
                refine ⟨47203915381731386043358301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31469276921154257362238867 47203915381731386043358301)
                ·
                  refine ⟨17701468268149269766259363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47203915381731386043358301 17701468268149269766259363)
                  ·
                    refine ⟨26552202402223904649389045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17701468268149269766259363 26552202402223904649389045)
                    ·
                      refine ⟨2489268975208491060880223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26552202402223904649389045 2489268975208491060880223)
                      ·
                        rfl

theorem cell23_4847834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_4847834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847834 prefixEnd_4847834 := by exact prefixLift 4847834
  have htrace : WordTrace (prefixWord ++ tailWord_4847834) baseStart_4847834 baseEnd_4847834 := by
    simpa [prefixWord, tailWord_4847834, baseEnd_4847834] using wordTrace_append hprefix tailTrace_4847834
  have hstable : (prefixWord ++ tailWord_4847834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847834).length < 2 ^ (prefixWord ++ tailWord_4847834).sum := by decide
  have hdescent : baseEnd_4847834 < baseStart_4847834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847848 : List Nat := [2, 1, 4, 1, 2, 3, 2, 2, 1, 1, 4]
def baseStart_4847848 : Nat := 118140960795 + 4847848 * 2 ^ 59
def prefixEnd_4847848 : Nat := 4983230072969 + 3 ^ 40 * 4847848 * 2
def baseEnd_4847848 : Nat := 2489276163937654006105159

theorem tailTrace_4847848 : CollatzResearch.WordTrace tailWord_4847848 prefixEnd_4847848 2489276163937654006105159 := by
  unfold tailWord_4847848
  simp only [CollatzResearch.WordTrace]
  refine ⟨88407771270541058683660099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117877028360721411578213465 88407771270541058683660099)
  ·
    refine ⟨132611656905811588025490149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88407771270541058683660099 132611656905811588025490149)
    ·
      refine ⟨24864685669839672754779403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132611656905811588025490149 24864685669839672754779403)
      ·
        refine ⟨37297028504759509132169105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24864685669839672754779403 37297028504759509132169105)
        ·
          refine ⟨27972771378569631849126829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37297028504759509132169105 27972771378569631849126829)
          ·
            refine ⟨10489789266963611943422561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27972771378569631849126829 10489789266963611943422561)
            ·
              refine ⟨7867341950222708957566921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10489789266963611943422561 7867341950222708957566921)
              ·
                refine ⟨5900506462667031718175191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7867341950222708957566921 5900506462667031718175191)
                ·
                  refine ⟨8850759694000547577262787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5900506462667031718175191 8850759694000547577262787)
                  ·
                    refine ⟨13276139541000821365894181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8850759694000547577262787 13276139541000821365894181)
                    ·
                      refine ⟨2489276163937654006105159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13276139541000821365894181 2489276163937654006105159)
                      ·
                        rfl

theorem cell23_4847848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_4847848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847848 prefixEnd_4847848 := by exact prefixLift 4847848
  have htrace : WordTrace (prefixWord ++ tailWord_4847848) baseStart_4847848 baseEnd_4847848 := by
    simpa [prefixWord, tailWord_4847848, baseEnd_4847848] using wordTrace_append hprefix tailTrace_4847848
  have hstable : (prefixWord ++ tailWord_4847848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847848).length < 2 ^ (prefixWord ++ tailWord_4847848).sum := by decide
  have hdescent : baseEnd_4847848 < baseStart_4847848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847865 : List Nat := [1, 2, 1, 3, 1, 1, 2, 7, 1, 2, 2]
def baseStart_4847865 : Nat := 118140960795 + 4847865 * 2 ^ 59
def prefixEnd_4847865 : Nat := 4983230072969 + 3 ^ 40 * 4847865 * 2
def baseEnd_4847865 : Nat := 2489284893108780439592581

theorem tailTrace_4847865 : CollatzResearch.WordTrace tailWord_4847865 prefixEnd_4847865 2489284893108780439592581 := by
  unfold tailWord_4847865
  simp only [CollatzResearch.WordTrace]
  refine ⟨176816162582020529270689049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117877441721347019513792699 176816162582020529270689049)
  ·
    refine ⟨132612121936515396953016787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176816162582020529270689049 132612121936515396953016787)
    ·
      refine ⟨198918182904773095429525181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132612121936515396953016787 198918182904773095429525181)
      ·
        refine ⟨74594318589289910786071943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198918182904773095429525181 74594318589289910786071943)
        ·
          refine ⟨111891477883934866179107915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74594318589289910786071943 111891477883934866179107915)
          ·
            refine ⟨167837216825902299268661873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111891477883934866179107915 167837216825902299268661873)
            ·
              refine ⟨125877912619426724451496405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167837216825902299268661873 125877912619426724451496405)
              ·
                refine ⟨2950263577017813854331947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 125877912619426724451496405 2950263577017813854331947)
                ·
                  refine ⟨4425395365526720781497921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2950263577017813854331947 4425395365526720781497921)
                  ·
                    refine ⟨3319046524145040586123441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4425395365526720781497921 3319046524145040586123441)
                    ·
                      refine ⟨2489284893108780439592581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3319046524145040586123441 2489284893108780439592581)
                      ·
                        rfl

theorem cell23_4847865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_4847865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847865 prefixEnd_4847865 := by exact prefixLift 4847865
  have htrace : WordTrace (prefixWord ++ tailWord_4847865) baseStart_4847865 baseEnd_4847865 := by
    simpa [prefixWord, tailWord_4847865, baseEnd_4847865] using wordTrace_append hprefix tailTrace_4847865
  have hstable : (prefixWord ++ tailWord_4847865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847865).length < 2 ^ (prefixWord ++ tailWord_4847865).sum := by decide
  have hdescent : baseEnd_4847865 < baseStart_4847865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847868 : List Nat := [2, 2, 2, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_4847868 : Nat := 118140960795 + 4847868 * 2 ^ 59
def prefixEnd_4847868 : Nat := 4983230072969 + 3 ^ 40 * 4847868 * 2
def baseEnd_4847868 : Nat := 2489286433550743927855067

theorem tailTrace_4847868 : CollatzResearch.WordTrace tailWord_4847868 prefixEnd_4847868 2489286433550743927855067 := by
  unfold tailWord_4847868
  simp only [CollatzResearch.WordTrace]
  refine ⟨88408136000504830391524129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117877514667339773855365505 88408136000504830391524129)
  ·
    refine ⟨66306102000378622793643097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88408136000504830391524129 66306102000378622793643097)
    ·
      refine ⟨49729576500283967095232323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66306102000378622793643097 49729576500283967095232323)
      ·
        refine ⟨74594364750425950642848485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49729576500283967095232323 74594364750425950642848485)
        ·
          refine ⟨13986443390704865745534091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74594364750425950642848485 13986443390704865745534091)
          ·
            refine ⟨20979665086057298618301137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13986443390704865745534091 20979665086057298618301137)
            ·
              refine ⟨15734748814542973963725853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20979665086057298618301137 15734748814542973963725853)
              ·
                refine ⟨5900530805453615236397195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15734748814542973963725853 5900530805453615236397195)
                ·
                  refine ⟨8850796208180422854595793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5900530805453615236397195 8850796208180422854595793)
                  ·
                    refine ⟨6638097156135317140946845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8850796208180422854595793 6638097156135317140946845)
                    ·
                      refine ⟨2489286433550743927855067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6638097156135317140946845 2489286433550743927855067)
                      ·
                        rfl

theorem cell23_4847868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_4847868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847868 prefixEnd_4847868 := by exact prefixLift 4847868
  have htrace : WordTrace (prefixWord ++ tailWord_4847868) baseStart_4847868 baseEnd_4847868 := by
    simpa [prefixWord, tailWord_4847868, baseEnd_4847868] using wordTrace_append hprefix tailTrace_4847868
  have hstable : (prefixWord ++ tailWord_4847868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847868).length < 2 ^ (prefixWord ++ tailWord_4847868).sum := by decide
  have hdescent : baseEnd_4847868 < baseStart_4847868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847884 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 2, 7]
def baseStart_4847884 : Nat := 118140960795 + 4847884 * 2 ^ 59
def prefixEnd_4847884 : Nat := 4983230072969 + 3 ^ 40 * 4847884 * 2
def baseEnd_4847884 : Nat := 829764883080405288418331

theorem tailTrace_4847884 : CollatzResearch.WordTrace tailWord_4847884 prefixEnd_4847884 829764883080405288418331 := by
  unfold tailWord_4847884
  simp only [CollatzResearch.WordTrace]
  refine ⟨88408427784475847757815353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117877903712634463677087137 88408427784475847757815353)
  ·
    refine ⟨66306320838356885818361515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88408427784475847757815353 66306320838356885818361515)
    ·
      refine ⟨99459481257535328727542273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66306320838356885818361515 99459481257535328727542273)
      ·
        refine ⟨74594610943151496545656705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99459481257535328727542273 74594610943151496545656705)
        ·
          refine ⟨55945958207363622409242529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74594610943151496545656705 55945958207363622409242529)
          ·
            refine ⟨41959468655522716806931897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55945958207363622409242529 41959468655522716806931897)
            ·
              refine ⟨31469601491642037605198923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41959468655522716806931897 31469601491642037605198923)
              ·
                refine ⟨47204402237463056407798385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31469601491642037605198923 47204402237463056407798385)
                ·
                  refine ⟨35403301678097292305848789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47204402237463056407798385 35403301678097292305848789)
                  ·
                    refine ⟨829764883080405288418331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35403301678097292305848789 829764883080405288418331)
                    ·
                      rfl

theorem cell23_4847884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_4847884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847884 prefixEnd_4847884 := by exact prefixLift 4847884
  have htrace : WordTrace (prefixWord ++ tailWord_4847884) baseStart_4847884 baseEnd_4847884 := by
    simpa [prefixWord, tailWord_4847884, baseEnd_4847884] using wordTrace_append hprefix tailTrace_4847884
  have hstable : (prefixWord ++ tailWord_4847884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847884).length < 2 ^ (prefixWord ++ tailWord_4847884).sum := by decide
  have hdescent : baseEnd_4847884 < baseStart_4847884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847902 : List Nat := [4, 3, 2, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_4847902 : Nat := 118140960795 + 4847902 * 2 ^ 59
def prefixEnd_4847902 : Nat := 4983230072969 + 3 ^ 40 * 4847902 * 2
def baseEnd_4847902 : Nat := 2489303891892996794829911

theorem tailTrace_4847902 : CollatzResearch.WordTrace tailWord_4847902 prefixEnd_4847902 2489303891892996794829911 := by
  unfold tailWord_4847902
  simp only [CollatzResearch.WordTrace]
  refine ⟨22102189010360810573723245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117878341388590989726523973 22102189010360810573723245)
  ·
    refine ⟨8288320878885303965146217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22102189010360810573723245 8288320878885303965146217)
    ·
      refine ⟨6216240659163977973859663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8288320878885303965146217 6216240659163977973859663)
      ·
        refine ⟨9324360988745966960789495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6216240659163977973859663 9324360988745966960789495)
        ·
          refine ⟨13986541483118950441184243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9324360988745966960789495 13986541483118950441184243)
          ·
            refine ⟨20979812224678425661776365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13986541483118950441184243 20979812224678425661776365)
            ·
              refine ⟨7867429584254409623166137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20979812224678425661776365 7867429584254409623166137)
              ·
                refine ⟨5900572188190807217374603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7867429584254409623166137 5900572188190807217374603)
                ·
                  refine ⟨8850858282286210826061905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5900572188190807217374603 8850858282286210826061905)
                  ·
                    refine ⟨6638143711714658119546429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8850858282286210826061905 6638143711714658119546429)
                    ·
                      refine ⟨2489303891892996794829911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6638143711714658119546429 2489303891892996794829911)
                      ·
                        rfl

theorem cell23_4847902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_4847902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847902 prefixEnd_4847902 := by exact prefixLift 4847902
  have htrace : WordTrace (prefixWord ++ tailWord_4847902) baseStart_4847902 baseEnd_4847902 := by
    simpa [prefixWord, tailWord_4847902, baseEnd_4847902] using wordTrace_append hprefix tailTrace_4847902
  have hstable : (prefixWord ++ tailWord_4847902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847902).length < 2 ^ (prefixWord ++ tailWord_4847902).sum := by decide
  have hdescent : baseEnd_4847902 < baseStart_4847902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847971 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 3]
def baseStart_4847971 : Nat := 118140960795 + 4847971 * 2 ^ 59
def prefixEnd_4847971 : Nat := 4983230072969 + 3 ^ 40 * 4847971 * 2
def baseEnd_4847971 : Nat := 2489339322058157024867093

theorem tailTrace_4847971 : CollatzResearch.WordTrace tailWord_4847971 prefixEnd_4847971 2489339322058157024867093 := by
  unfold tailWord_4847971
  simp only [CollatzResearch.WordTrace]
  refine ⟨176820028719636509374047767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117880019146424339582698511 176820028719636509374047767)
  ·
    refine ⟨265230043079454764061071651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176820028719636509374047767 265230043079454764061071651)
    ·
      refine ⟨397845064619182146091607477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265230043079454764061071651 397845064619182146091607477)
      ·
        refine ⟨37297974808048326196088201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 397845064619182146091607477 37297974808048326196088201)
        ·
          refine ⟨27973481106036244647066151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37297974808048326196088201 27973481106036244647066151)
          ·
            refine ⟨41960221659054366970599227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27973481106036244647066151 41960221659054366970599227)
            ·
              refine ⟨62940332488581550455898841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41960221659054366970599227 62940332488581550455898841)
              ·
                refine ⟨47205249366436162841924131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62940332488581550455898841 47205249366436162841924131)
                ·
                  refine ⟨70807874049654244262886197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47205249366436162841924131 70807874049654244262886197)
                  ·
                    refine ⟨6638238192155085399645581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70807874049654244262886197 6638238192155085399645581)
                    ·
                      refine ⟨2489339322058157024867093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6638238192155085399645581 2489339322058157024867093)
                      ·
                        rfl

theorem cell23_4847971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_4847971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847971 prefixEnd_4847971 := by exact prefixLift 4847971
  have htrace : WordTrace (prefixWord ++ tailWord_4847971) baseStart_4847971 baseEnd_4847971 := by
    simpa [prefixWord, tailWord_4847971, baseEnd_4847971] using wordTrace_append hprefix tailTrace_4847971
  have hstable : (prefixWord ++ tailWord_4847971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847971).length < 2 ^ (prefixWord ++ tailWord_4847971).sum := by decide
  have hdescent : baseEnd_4847971 < baseStart_4847971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4847989 : List Nat := [1, 3, 4, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_4847989 : Nat := 118140960795 + 4847989 * 2 ^ 59
def prefixEnd_4847989 : Nat := 4983230072969 + 3 ^ 40 * 4847989 * 2
def baseEnd_4847989 : Nat := 2489348564709937954442011

theorem tailTrace_4847989 : CollatzResearch.WordTrace tailWord_4847989 prefixEnd_4847989 2489348564709937954442011 := by
  unfold tailWord_4847989
  simp only [CollatzResearch.WordTrace]
  refine ⟨176820685233571298448203021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117880456822380865632135347 176820685233571298448203021)
  ·
    refine ⟨66307756962589236918076133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176820685233571298448203021 66307756962589236918076133)
    ·
      refine ⟨12432704430485481922139275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66307756962589236918076133 12432704430485481922139275)
      ·
        refine ⟨18649056645728222883208913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12432704430485481922139275 18649056645728222883208913)
        ·
          refine ⟨13986792484296167162406685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18649056645728222883208913 13986792484296167162406685)
          ·
            refine ⟨5245047181611062685902507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13986792484296167162406685 5245047181611062685902507)
            ·
              refine ⟨7867570772416594028853761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5245047181611062685902507 7867570772416594028853761)
              ·
                refine ⟨5900678079312445521640321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7867570772416594028853761 5900678079312445521640321)
                ·
                  refine ⟨4425508559484334141230241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5900678079312445521640321 4425508559484334141230241)
                  ·
                    refine ⟨3319131419613250605922681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4425508559484334141230241 3319131419613250605922681)
                    ·
                      refine ⟨2489348564709937954442011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3319131419613250605922681 2489348564709937954442011)
                      ·
                        rfl

theorem cell23_4847989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_4847989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4847989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4847989 prefixEnd_4847989 := by exact prefixLift 4847989
  have htrace : WordTrace (prefixWord ++ tailWord_4847989) baseStart_4847989 baseEnd_4847989 := by
    simpa [prefixWord, tailWord_4847989, baseEnd_4847989] using wordTrace_append hprefix tailTrace_4847989
  have hstable : (prefixWord ++ tailWord_4847989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4847989).length < 2 ^ (prefixWord ++ tailWord_4847989).sum := by decide
  have hdescent : baseEnd_4847989 < baseStart_4847989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4847989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848011 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 4]
def baseStart_4848011 : Nat := 118140960795 + 4848011 * 2 ^ 59
def prefixEnd_4848011 : Nat := 4983230072969 + 3 ^ 40 * 4848011 * 2
def baseEnd_4848011 : Nat := 2489359861284336868366909

theorem tailTrace_4848011 : CollatzResearch.WordTrace tailWord_4848011 prefixEnd_4848011 2489359861284336868366909 := by
  unfold tailWord_4848011
  simp only [CollatzResearch.WordTrace]
  refine ⟨176821487639491596205503887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117880991759661064137002591 176821487639491596205503887)
  ·
    refine ⟨265232231459237394308255831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176821487639491596205503887 265232231459237394308255831)
    ·
      refine ⟨397848347188856091462383747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265232231459237394308255831 397848347188856091462383747)
      ·
        refine ⟨596772520783284137193575621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397848347188856091462383747 596772520783284137193575621)
        ·
          refine ⟨111894847646865775723795429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 596772520783284137193575621 111894847646865775723795429)
          ·
            refine ⟨20980283933787332948211643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111894847646865775723795429 20980283933787332948211643)
            ·
              refine ⟨31470425900680999422317465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20980283933787332948211643 31470425900680999422317465)
              ·
                refine ⟨23602819425510749566738099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31470425900680999422317465 23602819425510749566738099)
                ·
                  refine ⟨35404229138266124350107149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23602819425510749566738099 35404229138266124350107149)
                  ·
                    refine ⟨13276585926849796631290181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35404229138266124350107149 13276585926849796631290181)
                    ·
                      refine ⟨2489359861284336868366909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13276585926849796631290181 2489359861284336868366909)
                      ·
                        rfl

theorem cell23_4848011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 4].length) (baseStart_4848011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848011 prefixEnd_4848011 := by exact prefixLift 4848011
  have htrace : WordTrace (prefixWord ++ tailWord_4848011) baseStart_4848011 baseEnd_4848011 := by
    simpa [prefixWord, tailWord_4848011, baseEnd_4848011] using wordTrace_append hprefix tailTrace_4848011
  have hstable : (prefixWord ++ tailWord_4848011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848011).length < 2 ^ (prefixWord ++ tailWord_4848011).sum := by decide
  have hdescent : baseEnd_4848011 < baseStart_4848011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848052 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_4848052 : Nat := 118140960795 + 4848052 * 2 ^ 59
def prefixEnd_4848052 : Nat := 4983230072969 + 3 ^ 40 * 4848052 * 2
def baseEnd_4848052 : Nat := 2489380913991171207954221

theorem tailTrace_4848052 : CollatzResearch.WordTrace tailWord_4848052 prefixEnd_4848052 2489380913991171207954221 := by
  unfold tailWord_4848052
  simp only [CollatzResearch.WordTrace]
  refine ⟨88411491516171530103873205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117881988688228706805164273 88411491516171530103873205)
  ·
    refine ⟨8288577329641080947238113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88411491516171530103873205 8288577329641080947238113)
    ·
      refine ⟨6216432997230810710428585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8288577329641080947238113 6216432997230810710428585)
      ·
        refine ⟨4662324747923108032821439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6216432997230810710428585 4662324747923108032821439)
        ·
          refine ⟨6993487121884662049232159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4662324747923108032821439 6993487121884662049232159)
          ·
            refine ⟨10490230682826993073848239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6993487121884662049232159 10490230682826993073848239)
            ·
              refine ⟨15735346024240489610772359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10490230682826993073848239 15735346024240489610772359)
              ·
                refine ⟨23603019036360734416158539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15735346024240489610772359 23603019036360734416158539)
                ·
                  refine ⟨35404528554541101624237809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23603019036360734416158539 35404528554541101624237809)
                  ·
                    refine ⟨26553396415905826218178357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35404528554541101624237809 26553396415905826218178357)
                    ·
                      refine ⟨2489380913991171207954221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26553396415905826218178357 2489380913991171207954221)
                      ·
                        rfl

theorem cell23_4848052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_4848052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848052 prefixEnd_4848052 := by exact prefixLift 4848052
  have htrace : WordTrace (prefixWord ++ tailWord_4848052) baseStart_4848052 baseEnd_4848052 := by
    simpa [prefixWord, tailWord_4848052, baseEnd_4848052] using wordTrace_append hprefix tailTrace_4848052
  have hstable : (prefixWord ++ tailWord_4848052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848052).length < 2 ^ (prefixWord ++ tailWord_4848052).sum := by decide
  have hdescent : baseEnd_4848052 < baseStart_4848052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848055 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 3, 4]
def baseStart_4848055 : Nat := 118140960795 + 4848055 * 2 ^ 59
def prefixEnd_4848055 : Nat := 4983230072969 + 3 ^ 40 * 4848055 * 2
def baseEnd_4848055 : Nat := 829794151477711565405569

theorem tailTrace_4848055 : CollatzResearch.WordTrace tailWord_4848055 prefixEnd_4848055 829794151477711565405569 := by
  unfold tailWord_4848055
  simp only [CollatzResearch.WordTrace]
  refine ⟨176823092451332191720105619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117882061634221461146737079 176823092451332191720105619)
  ·
    refine ⟨265234638676998287580158429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176823092451332191720105619 265234638676998287580158429)
    ·
      refine ⟨99462989503874357842559411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265234638676998287580158429 99462989503874357842559411)
      ·
        refine ⟨149194484255811536763839117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99462989503874357842559411 149194484255811536763839117)
        ·
          refine ⟨55947931595929326286439669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149194484255811536763839117 55947931595929326286439669)
          ·
            refine ⟨5245118587118374339353719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55947931595929326286439669 5245118587118374339353719)
            ·
              refine ⟨7867677880677561509030579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5245118587118374339353719 7867677880677561509030579)
              ·
                refine ⟨11801516821016342263545869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7867677880677561509030579 11801516821016342263545869)
                ·
                  refine ⟨4425568807881128348829701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11801516821016342263545869 4425568807881128348829701)
                  ·
                    refine ⟨829794151477711565405569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4425568807881128348829701 829794151477711565405569)
                    ·
                      rfl

theorem cell23_4848055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 4].length) (baseStart_4848055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848055 prefixEnd_4848055 := by exact prefixLift 4848055
  have htrace : WordTrace (prefixWord ++ tailWord_4848055) baseStart_4848055 baseEnd_4848055 := by
    simpa [prefixWord, tailWord_4848055, baseEnd_4848055] using wordTrace_append hprefix tailTrace_4848055
  have hstable : (prefixWord ++ tailWord_4848055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848055).length < 2 ^ (prefixWord ++ tailWord_4848055).sum := by decide
  have hdescent : baseEnd_4848055 < baseStart_4848055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848111 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 5, 6]
def baseStart_4848111 : Nat := 118140960795 + 4848111 * 2 ^ 59
def prefixEnd_4848111 : Nat := 4983230072969 + 3 ^ 40 * 4848111 * 2
def baseEnd_4848111 : Nat := 829803736449928825705483

theorem tailTrace_4848111 : CollatzResearch.WordTrace tailWord_4848111 prefixEnd_4848111 829803736449928825705483 := by
  unfold tailWord_4848111
  simp only [CollatzResearch.WordTrace]
  refine ⟨176825134939129313284144187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117883423292752875522762791 176825134939129313284144187)
  ·
    refine ⟨265237702408693969926216281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176825134939129313284144187 265237702408693969926216281)
    ·
      refine ⟨198928276806520477444662211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265237702408693969926216281 198928276806520477444662211)
      ·
        refine ⟨298392415209780716166993317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198928276806520477444662211 298392415209780716166993317)
        ·
          refine ⟨55948577851833884281311247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 298392415209780716166993317 55948577851833884281311247)
          ·
            refine ⟨83922866777750826421966871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55948577851833884281311247 83922866777750826421966871)
            ·
              refine ⟨125884300166626239632950307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83922866777750826421966871 125884300166626239632950307)
              ·
                refine ⟨188826450249939359449425461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125884300166626239632950307 188826450249939359449425461)
                ·
                  refine ⟨17702479710931814948383637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188826450249939359449425461 17702479710931814948383637)
                  ·
                    refine ⟨829803736449928825705483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17702479710931814948383637 829803736449928825705483)
                    ·
                      rfl

theorem cell23_4848111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_4848111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848111 prefixEnd_4848111 := by exact prefixLift 4848111
  have htrace : WordTrace (prefixWord ++ tailWord_4848111) baseStart_4848111 baseEnd_4848111 := by
    simpa [prefixWord, tailWord_4848111, baseEnd_4848111] using wordTrace_append hprefix tailTrace_4848111
  have hstable : (prefixWord ++ tailWord_4848111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848111).length < 2 ^ (prefixWord ++ tailWord_4848111).sum := by decide
  have hdescent : baseEnd_4848111 < baseStart_4848111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848112 : List Nat := [2, 1, 1, 1, 3, 3, 3, 4, 1, 1, 3]
def baseStart_4848112 : Nat := 118140960795 + 4848112 * 2 ^ 59
def prefixEnd_4848112 : Nat := 4983230072969 + 3 ^ 40 * 4848112 * 2
def baseEnd_4848112 : Nat := 2489411722830440973203945

theorem tailTrace_4848112 : CollatzResearch.WordTrace tailWord_4848112 prefixEnd_4848112 2489411722830440973203945 := by
  unfold tailWord_4848112
  simp only [CollatzResearch.WordTrace]
  refine ⟨88412585706062845227465295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117883447608083793636620393 88412585706062845227465295)
  ·
    refine ⟨132618878559094267841197943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88412585706062845227465295 132618878559094267841197943)
    ·
      refine ⟨198928317838641401761796915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132618878559094267841197943 198928317838641401761796915)
      ·
        refine ⟨298392476757962102642695373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198928317838641401761796915 298392476757962102642695373)
        ·
          refine ⟨111897178784235788491010765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 298392476757962102642695373 111897178784235788491010765)
          ·
            refine ⟨41961442044088420684129037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111897178784235788491010765 41961442044088420684129037)
            ·
              refine ⟨15735540766533157756548389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41961442044088420684129037 15735540766533157756548389)
              ·
                refine ⟨2950413893724967079352823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15735540766533157756548389 2950413893724967079352823)
                ·
                  refine ⟨4425620840587450619029235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2950413893724967079352823 4425620840587450619029235)
                  ·
                    refine ⟨6638431260881175928543853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4425620840587450619029235 6638431260881175928543853)
                    ·
                      refine ⟨2489411722830440973203945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6638431260881175928543853 2489411722830440973203945)
                      ·
                        rfl

theorem cell23_4848112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 1, 1, 3].length) (baseStart_4848112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848112 prefixEnd_4848112 := by exact prefixLift 4848112
  have htrace : WordTrace (prefixWord ++ tailWord_4848112) baseStart_4848112 baseEnd_4848112 := by
    simpa [prefixWord, tailWord_4848112, baseEnd_4848112] using wordTrace_append hprefix tailTrace_4848112
  have hstable : (prefixWord ++ tailWord_4848112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848112).length < 2 ^ (prefixWord ++ tailWord_4848112).sum := by decide
  have hdescent : baseEnd_4848112 < baseStart_4848112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848152 : List Nat := [2, 1, 2, 3, 3, 1, 4, 1, 1, 1, 4]
def baseStart_4848152 : Nat := 118140960795 + 4848152 * 2 ^ 59
def prefixEnd_4848152 : Nat := 4983230072969 + 3 ^ 40 * 4848152 * 2
def baseEnd_4848152 : Nat := 2489432262056620816703761

theorem tailTrace_4848152 : CollatzResearch.WordTrace tailWord_4848152 prefixEnd_4848152 2489432262056620816703761 := by
  unfold tailWord_4848152
  simp only [CollatzResearch.WordTrace]
  refine ⟨88413315165990388643193355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117884420221320518190924473 88413315165990388643193355)
  ·
    refine ⟨132619972748985582964790033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88413315165990388643193355 132619972748985582964790033)
    ·
      refine ⟨99464979561739187223592525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132619972748985582964790033 99464979561739187223592525)
      ·
        refine ⟨37299367335652195208847197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99464979561739187223592525 37299367335652195208847197)
        ·
          refine ⟨13987262750869573203317699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37299367335652195208847197 13987262750869573203317699)
          ·
            refine ⟨20980894126304359804976549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13987262750869573203317699 20980894126304359804976549)
            ·
              refine ⟨3933917648682067463433103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20980894126304359804976549 3933917648682067463433103)
              ·
                refine ⟨5900876473023101195149655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933917648682067463433103 5900876473023101195149655)
                ·
                  refine ⟨8851314709534651792724483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5900876473023101195149655 8851314709534651792724483)
                  ·
                    refine ⟨13276972064301977689086725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8851314709534651792724483 13276972064301977689086725)
                    ·
                      refine ⟨2489432262056620816703761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13276972064301977689086725 2489432262056620816703761)
                      ·
                        rfl

theorem cell23_4848152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_4848152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848152 prefixEnd_4848152 := by exact prefixLift 4848152
  have htrace : WordTrace (prefixWord ++ tailWord_4848152) baseStart_4848152 baseEnd_4848152 := by
    simpa [prefixWord, tailWord_4848152, baseEnd_4848152] using wordTrace_append hprefix tailTrace_4848152
  have hstable : (prefixWord ++ tailWord_4848152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848152).length < 2 ^ (prefixWord ++ tailWord_4848152).sum := by decide
  have hdescent : baseEnd_4848152 < baseStart_4848152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848171 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 1, 9]
def baseStart_4848171 : Nat := 118140960795 + 4848171 * 2 ^ 59
def prefixEnd_4848171 : Nat := 4983230072969 + 3 ^ 40 * 4848171 * 2
def baseEnd_4848171 : Nat := 829814006063018747455391

theorem tailTrace_4848171 : CollatzResearch.WordTrace tailWord_4848171 prefixEnd_4848171 829814006063018747455391 := by
  unfold tailWord_4848171
  simp only [CollatzResearch.WordTrace]
  refine ⟨176827323318911943531328367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117884882212607962354218911 176827323318911943531328367)
  ·
    refine ⟨265240984978367915296992551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176827323318911943531328367 265240984978367915296992551)
    ·
      refine ⟨397861477467551872945488827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265240984978367915296992551 397861477467551872945488827)
      ·
        refine ⟨596792216201327809418233241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397861477467551872945488827 596792216201327809418233241)
        ·
          refine ⟨447594162150995857063674931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 596792216201327809418233241 447594162150995857063674931)
          ·
            refine ⟨671391243226493785595512397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447594162150995857063674931 671391243226493785595512397)
            ·
              refine ⟨251771716209935169598317149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 671391243226493785595512397 251771716209935169598317149)
              ·
                refine ⟨94414393578725688599368931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251771716209935169598317149 94414393578725688599368931)
                ·
                  refine ⟨141621590368088532899053397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94414393578725688599368931 141621590368088532899053397)
                  ·
                    refine ⟨829814006063018747455391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 141621590368088532899053397 829814006063018747455391)
                    ·
                      rfl

theorem cell23_4848171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 9].length) (baseStart_4848171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848171 prefixEnd_4848171 := by exact prefixLift 4848171
  have htrace : WordTrace (prefixWord ++ tailWord_4848171) baseStart_4848171 baseEnd_4848171 := by
    simpa [prefixWord, tailWord_4848171, baseEnd_4848171] using wordTrace_append hprefix tailTrace_4848171
  have hstable : (prefixWord ++ tailWord_4848171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848171).length < 2 ^ (prefixWord ++ tailWord_4848171).sum := by decide
  have hdescent : baseEnd_4848171 < baseStart_4848171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848182 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4]
def baseStart_4848182 : Nat := 118140960795 + 4848182 * 2 ^ 59
def prefixEnd_4848182 : Nat := 4983230072969 + 3 ^ 40 * 4848182 * 2
def baseEnd_4848182 : Nat := 2489447666476255699328623

theorem tailTrace_4848182 : CollatzResearch.WordTrace tailWord_4848182 prefixEnd_4848182 2489447666476255699328623 := by
  unfold tailWord_4848182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11051732782617005775623675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117885149681248061606652533 11051732782617005775623675)
  ·
    refine ⟨16577599173925508663435513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11051732782617005775623675 16577599173925508663435513)
    ·
      refine ⟨12433199380444131497576635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16577599173925508663435513 12433199380444131497576635)
      ·
        refine ⟨18649799070666197246364953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12433199380444131497576635 18649799070666197246364953)
        ·
          refine ⟨13987349302999647934773715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18649799070666197246364953 13987349302999647934773715)
          ·
            refine ⟨20981023954499471902160573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13987349302999647934773715 20981023954499471902160573)
            ·
              refine ⟨7867883982937301963310215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20981023954499471902160573 7867883982937301963310215)
              ·
                refine ⟨11801825974405952944965323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7867883982937301963310215 11801825974405952944965323)
                ·
                  refine ⟨17702738961608929417447985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11801825974405952944965323 17702738961608929417447985)
                  ·
                    refine ⟨13277054221206697063085989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17702738961608929417447985 13277054221206697063085989)
                    ·
                      refine ⟨2489447666476255699328623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13277054221206697063085989 2489447666476255699328623)
                      ·
                        rfl

theorem cell23_4848182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_4848182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848182 prefixEnd_4848182 := by exact prefixLift 4848182
  have htrace : WordTrace (prefixWord ++ tailWord_4848182) baseStart_4848182 baseEnd_4848182 := by
    simpa [prefixWord, tailWord_4848182, baseEnd_4848182] using wordTrace_append hprefix tailTrace_4848182
  have hstable : (prefixWord ++ tailWord_4848182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848182).length < 2 ^ (prefixWord ++ tailWord_4848182).sum := by decide
  have hdescent : baseEnd_4848182 < baseStart_4848182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848195 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 3, 3, 2]
def baseStart_4848195 : Nat := 118140960795 + 4848195 * 2 ^ 59
def prefixEnd_4848195 : Nat := 4983230072969 + 3 ^ 40 * 4848195 * 2
def baseEnd_4848195 : Nat := 2489454341724764148466063

theorem tailTrace_4848195 : CollatzResearch.WordTrace tailWord_4848195 prefixEnd_4848195 2489454341724764148466063 := by
  unfold tailWord_4848195
  simp only [CollatzResearch.WordTrace]
  refine ⟨176828198670824995630202039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117885465780549997086801359 176828198670824995630202039)
  ·
    refine ⟨265242298006237493445303059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176828198670824995630202039 265242298006237493445303059)
    ·
      refine ⟨397863447009356240167954589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265242298006237493445303059 397863447009356240167954589)
      ·
        refine ⟨149198792628508590062982971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 397863447009356240167954589 149198792628508590062982971)
        ·
          refine ⟨223798188942762885094474457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149198792628508590062982971 223798188942762885094474457)
          ·
            refine ⟨167848641707072163820855843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223798188942762885094474457 167848641707072163820855843)
            ·
              refine ⟨251772962560608245731283765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167848641707072163820855843 251772962560608245731283765)
              ·
                refine ⟨23603715240057023037307853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 251772962560608245731283765 23603715240057023037307853)
                ·
                  refine ⟨8851393215021383638990445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23603715240057023037307853 8851393215021383638990445)
                  ·
                    refine ⟨3319272455633018864621417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8851393215021383638990445 3319272455633018864621417)
                    ·
                      refine ⟨2489454341724764148466063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3319272455633018864621417 2489454341724764148466063)
                      ·
                        rfl

theorem cell23_4848195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 3, 2].length) (baseStart_4848195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848195 prefixEnd_4848195 := by exact prefixLift 4848195
  have htrace : WordTrace (prefixWord ++ tailWord_4848195) baseStart_4848195 baseEnd_4848195 := by
    simpa [prefixWord, tailWord_4848195, baseEnd_4848195] using wordTrace_append hprefix tailTrace_4848195
  have hstable : (prefixWord ++ tailWord_4848195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848195).length < 2 ^ (prefixWord ++ tailWord_4848195).sum := by decide
  have hdescent : baseEnd_4848195 < baseStart_4848195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848228 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_4848228 : Nat := 118140960795 + 4848228 * 2 ^ 59
def prefixEnd_4848228 : Nat := 4983230072969 + 3 ^ 40 * 4848228 * 2
def baseEnd_4848228 : Nat := 2489471286586362519353411

theorem tailTrace_4848228 : CollatzResearch.WordTrace tailWord_4848228 prefixEnd_4848228 2489471286586362519353411 := by
  unfold tailWord_4848228
  simp only [CollatzResearch.WordTrace]
  refine ⟨88414701139852721133076669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117886268186470294844102225 88414701139852721133076669)
  ·
    refine ⟨33155512927444770424903751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88414701139852721133076669 33155512927444770424903751)
    ·
      refine ⟨49733269391167155637355627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33155512927444770424903751 49733269391167155637355627)
      ·
        refine ⟨74599904086750733456033441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49733269391167155637355627 74599904086750733456033441)
        ·
          refine ⟨55949928065063050092025081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74599904086750733456033441 55949928065063050092025081)
          ·
            refine ⟨41962446048797287569018811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55949928065063050092025081 41962446048797287569018811)
            ·
              refine ⟨62943669073195931353528217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41962446048797287569018811 62943669073195931353528217)
              ·
                refine ⟨47207751804896948515146163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62943669073195931353528217 47207751804896948515146163)
                ·
                  refine ⟨70811627707345422772719245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47207751804896948515146163 70811627707345422772719245)
                  ·
                    refine ⟨26554360390254533539769717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70811627707345422772719245 26554360390254533539769717)
                    ·
                      refine ⟨2489471286586362519353411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26554360390254533539769717 2489471286586362519353411)
                      ·
                        rfl

theorem cell23_4848228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_4848228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848228 prefixEnd_4848228 := by exact prefixLift 4848228
  have htrace : WordTrace (prefixWord ++ tailWord_4848228) baseStart_4848228 baseEnd_4848228 := by
    simpa [prefixWord, tailWord_4848228, baseEnd_4848228] using wordTrace_append hprefix tailTrace_4848228
  have hstable : (prefixWord ++ tailWord_4848228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848228).length < 2 ^ (prefixWord ++ tailWord_4848228).sum := by decide
  have hdescent : baseEnd_4848228 < baseStart_4848228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848265 : List Nat := [1, 2, 1, 1, 4, 1, 1, 7, 5]
def baseStart_4848265 : Nat := 118140960795 + 4848265 * 2 ^ 59
def prefixEnd_4848265 : Nat := 4983230072969 + 3 ^ 40 * 4848265 * 2
def baseEnd_4848265 : Nat := 276610031707842097176749

theorem tailTrace_4848265 : CollatzResearch.WordTrace tailWord_4848265 prefixEnd_4848265 276610031707842097176749 := by
  unfold tailWord_4848265
  simp only [CollatzResearch.WordTrace]
  refine ⟨176830751780571397585250249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117887167853714265056833499 176830751780571397585250249)
  ·
    refine ⟨132623063835428548188937687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176830751780571397585250249 132623063835428548188937687)
    ·
      refine ⟨198934595753142822283406531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132623063835428548188937687 198934595753142822283406531)
      ·
        refine ⟨298401893629714233425109797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198934595753142822283406531 298401893629714233425109797)
        ·
          refine ⟨55950355055571418767208087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 298401893629714233425109797 55950355055571418767208087)
          ·
            refine ⟨83925532583357128150812131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55950355055571418767208087 83925532583357128150812131)
            ·
              refine ⟨125888298875035692226218197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83925532583357128150812131 125888298875035692226218197)
              ·
                refine ⟨2950507004883649036551989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 125888298875035692226218197 2950507004883649036551989)
                ·
                  refine ⟨276610031707842097176749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2950507004883649036551989 276610031707842097176749)
                  ·
                    rfl

theorem cell23_4848265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 5].length) (baseStart_4848265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848265 prefixEnd_4848265 := by exact prefixLift 4848265
  have htrace : WordTrace (prefixWord ++ tailWord_4848265) baseStart_4848265 baseEnd_4848265 := by
    simpa [prefixWord, tailWord_4848265, baseEnd_4848265] using wordTrace_append hprefix tailTrace_4848265
  have hstable : (prefixWord ++ tailWord_4848265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848265).length < 2 ^ (prefixWord ++ tailWord_4848265).sum := by decide
  have hdescent : baseEnd_4848265 < baseStart_4848265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848276 : List Nat := [2, 4, 2, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_4848276 : Nat := 118140960795 + 4848276 * 2 ^ 59
def prefixEnd_4848276 : Nat := 4983230072969 + 3 ^ 40 * 4848276 * 2
def baseEnd_4848276 : Nat := 2489495933657778331553191

theorem tailTrace_4848276 : CollatzResearch.WordTrace tailWord_4848276 prefixEnd_4848276 2489495933657778331553191 := by
  unfold tailWord_4848276
  simp only [CollatzResearch.WordTrace]
  refine ⟨88415576491765773231950341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117887435322354364309267121 88415576491765773231950341)
  ·
    refine ⟨16577920592206082480990689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88415576491765773231950341 16577920592206082480990689)
    ·
      refine ⟨12433440444154561860743017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16577920592206082480990689 12433440444154561860743017)
      ·
        refine ⟨9325080333115921395557263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12433440444154561860743017 9325080333115921395557263)
        ·
          refine ⟨13987620499673882093335895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9325080333115921395557263 13987620499673882093335895)
          ·
            refine ⟨20981430749510823140003843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13987620499673882093335895 20981430749510823140003843)
            ·
              refine ⟨31472146124266234710005765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20981430749510823140003843 31472146124266234710005765)
              ·
                refine ⟨5901027398299919008126081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31472146124266234710005765 5901027398299919008126081)
                ·
                  refine ⟨4425770548724939256094561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5901027398299919008126081 4425770548724939256094561)
                  ·
                    refine ⟨3319327911543704442070921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4425770548724939256094561 3319327911543704442070921)
                    ·
                      refine ⟨2489495933657778331553191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3319327911543704442070921 2489495933657778331553191)
                      ·
                        rfl

theorem cell23_4848276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_4848276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848276 prefixEnd_4848276 := by exact prefixLift 4848276
  have htrace : WordTrace (prefixWord ++ tailWord_4848276) baseStart_4848276 baseEnd_4848276 := by
    simpa [prefixWord, tailWord_4848276, baseEnd_4848276] using wordTrace_append hprefix tailTrace_4848276
  have hstable : (prefixWord ++ tailWord_4848276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848276).length < 2 ^ (prefixWord ++ tailWord_4848276).sum := by decide
  have hdescent : baseEnd_4848276 < baseStart_4848276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848385 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 5, 5]
def baseStart_4848385 : Nat := 118140960795 + 4848385 * 2 ^ 59
def prefixEnd_4848385 : Nat := 4983230072969 + 3 ^ 40 * 4848385 * 2
def baseEnd_4848385 : Nat := 829850634349706135030063

theorem tailTrace_4848385 : CollatzResearch.WordTrace tailWord_4848385 prefixEnd_4848385 829850634349706135030063 := by
  unfold tailWord_4848385
  simp only [CollatzResearch.WordTrace]
  refine ⟨176835128540136658079618609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117890085693424438719745739 176835128540136658079618609)
  ·
    refine ⟨132626346405102493559713957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176835128540136658079618609 132626346405102493559713957)
    ·
      refine ⟨24867439950956717542446367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132626346405102493559713957 24867439950956717542446367)
      ·
        refine ⟨37301159926435076313669551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24867439950956717542446367 37301159926435076313669551)
        ·
          refine ⟨55951739889652614470504327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37301159926435076313669551 55951739889652614470504327)
          ·
            refine ⟨83927609834478921705756491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55951739889652614470504327 83927609834478921705756491)
            ·
              refine ⟨125891414751718382558634737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83927609834478921705756491 125891414751718382558634737)
              ·
                refine ⟨94418561063788786918976053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125891414751718382558634737 94418561063788786918976053)
                ·
                  refine ⟨8851740099730198773654005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94418561063788786918976053 8851740099730198773654005)
                  ·
                    refine ⟨829850634349706135030063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8851740099730198773654005 829850634349706135030063)
                    ·
                      rfl

theorem cell23_4848385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_4848385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848385 prefixEnd_4848385 := by exact prefixLift 4848385
  have htrace : WordTrace (prefixWord ++ tailWord_4848385) baseStart_4848385 baseEnd_4848385 := by
    simpa [prefixWord, tailWord_4848385, baseEnd_4848385] using wordTrace_append hprefix tailTrace_4848385
  have hstable : (prefixWord ++ tailWord_4848385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848385).length < 2 ^ (prefixWord ++ tailWord_4848385).sum := by decide
  have hdescent : baseEnd_4848385 < baseStart_4848385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848425 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 2, 6, 3]
def baseStart_4848425 : Nat := 118140960795 + 4848425 * 2 ^ 59
def prefixEnd_4848425 : Nat := 4983230072969 + 3 ^ 40 * 4848425 * 2
def baseEnd_4848425 : Nat := 2489572442275298248590005

theorem tailTrace_4848425 : CollatzResearch.WordTrace tailWord_4848425 prefixEnd_4848425 2489572442275298248590005 := by
  unfold tailWord_4848425
  simp only [CollatzResearch.WordTrace]
  refine ⟨176836587459991744911074729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117891058306661163274049819 176836587459991744911074729)
  ·
    refine ⟨132627440594993808683306047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176836587459991744911074729 132627440594993808683306047)
    ·
      refine ⟨198941160892490713024959071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132627440594993808683306047 198941160892490713024959071)
      ·
        refine ⟨298411741338736069537438607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198941160892490713024959071 298411741338736069537438607)
        ·
          refine ⟨447617612008104104306157911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298411741338736069537438607 447617612008104104306157911)
          ·
            refine ⟨671426418012156156459236867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447617612008104104306157911 671426418012156156459236867)
            ·
              refine ⟨1007139627018234234688855301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671426418012156156459236867 1007139627018234234688855301)
              ·
                refine ⟨188838680065918919004160369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1007139627018234234688855301 188838680065918919004160369)
                ·
                  refine ⟨141629010049439189253120277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188838680065918919004160369 141629010049439189253120277)
                  ·
                    refine ⟨6638859846067461996240013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 141629010049439189253120277 6638859846067461996240013)
                    ·
                      refine ⟨2489572442275298248590005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6638859846067461996240013 2489572442275298248590005)
                      ·
                        rfl

theorem cell23_4848425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 6, 3].length) (baseStart_4848425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848425 prefixEnd_4848425 := by exact prefixLift 4848425
  have htrace : WordTrace (prefixWord ++ tailWord_4848425) baseStart_4848425 baseEnd_4848425 := by
    simpa [prefixWord, tailWord_4848425, baseEnd_4848425] using wordTrace_append hprefix tailTrace_4848425
  have hstable : (prefixWord ++ tailWord_4848425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848425).length < 2 ^ (prefixWord ++ tailWord_4848425).sum := by decide
  have hdescent : baseEnd_4848425 < baseStart_4848425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848439 : List Nat := [1, 1, 3, 1, 2, 1, 7, 1, 1, 1, 4]
def baseStart_4848439 : Nat := 118140960795 + 4848439 * 2 ^ 59
def prefixEnd_4848439 : Nat := 4983230072969 + 3 ^ 40 * 4848439 * 2
def baseEnd_4848439 : Nat := 2489579631004461193814941

theorem tailTrace_4848439 : CollatzResearch.WordTrace tailWord_4848439 prefixEnd_4848439 2489579631004461193814941 := by
  unfold tailWord_4848439
  simp only [CollatzResearch.WordTrace]
  refine ⟨176837098081941025302084371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117891398721294016868056247 176837098081941025302084371)
  ·
    refine ⟨265255647122911537953126557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176837098081941025302084371 265255647122911537953126557)
    ·
      refine ⟨99470867671091826732422459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265255647122911537953126557 99470867671091826732422459)
      ·
        refine ⟨149206301506637740098633689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99470867671091826732422459 149206301506637740098633689)
        ·
          refine ⟨111904726129978305073975267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149206301506637740098633689 111904726129978305073975267)
          ·
            refine ⟨167857089194967457610962901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111904726129978305073975267 167857089194967457610962901)
            ·
              refine ⟨3934150528007049787756943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 167857089194967457610962901 3934150528007049787756943)
              ·
                refine ⟨5901225792010574681635415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3934150528007049787756943 5901225792010574681635415)
                ·
                  refine ⟨8851838688015862022453123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5901225792010574681635415 8851838688015862022453123)
                  ·
                    refine ⟨13277758032023793033679685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8851838688015862022453123 13277758032023793033679685)
                    ·
                      refine ⟨2489579631004461193814941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13277758032023793033679685 2489579631004461193814941)
                      ·
                        rfl

theorem cell23_4848439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 1, 1, 4].length) (baseStart_4848439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848439 prefixEnd_4848439 := by exact prefixLift 4848439
  have htrace : WordTrace (prefixWord ++ tailWord_4848439) baseStart_4848439 baseEnd_4848439 := by
    simpa [prefixWord, tailWord_4848439, baseEnd_4848439] using wordTrace_append hprefix tailTrace_4848439
  have hstable : (prefixWord ++ tailWord_4848439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848439).length < 2 ^ (prefixWord ++ tailWord_4848439).sum := by decide
  have hdescent : baseEnd_4848439 < baseStart_4848439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848445 : List Nat := [1, 4, 1, 4, 13]
def baseStart_4848445 : Nat := 118140960795 + 4848445 * 2 ^ 59
def prefixEnd_4848445 : Nat := 4983230072969 + 3 ^ 40 * 4848445 * 2
def baseEnd_4848445 : Nat := 3415065448406568134897

theorem tailTrace_4848445 : CollatzResearch.WordTrace tailWord_4848445 prefixEnd_4848445 3415065448406568134897 := by
  unfold tailWord_4848445
  simp only [CollatzResearch.WordTrace]
  refine ⟨176837316919919288326802789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117891544613279525551201859 176837316919919288326802789)
  ·
    refine ⟨33156996922484866561275523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176837316919919288326802789 33156996922484866561275523)
    ·
      refine ⟨49735495383727299841913285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33156996922484866561275523 49735495383727299841913285)
      ·
        refine ⟨9325405384448868720358741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49735495383727299841913285 9325405384448868720358741)
        ·
          refine ⟨3415065448406568134897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9325405384448868720358741 3415065448406568134897)
          ·
            rfl

theorem cell23_4848445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 13].length) (baseStart_4848445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848445 prefixEnd_4848445 := by exact prefixLift 4848445
  have htrace : WordTrace (prefixWord ++ tailWord_4848445) baseStart_4848445 baseEnd_4848445 := by
    simpa [prefixWord, tailWord_4848445, baseEnd_4848445] using wordTrace_append hprefix tailTrace_4848445
  have hstable : (prefixWord ++ tailWord_4848445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848445).length < 2 ^ (prefixWord ++ tailWord_4848445).sum := by decide
  have hdescent : baseEnd_4848445 < baseStart_4848445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848569 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 7]
def baseStart_4848569 : Nat := 118140960795 + 4848569 * 2 ^ 59
def prefixEnd_4848569 : Nat := 4983230072969 + 3 ^ 40 * 4848569 * 2
def baseEnd_4848569 : Nat := 276627375943282853909927

theorem tailTrace_4848569 : CollatzResearch.WordTrace tailWord_4848569 prefixEnd_4848569 276627375943282853909927 := by
  unfold tailWord_4848569
  simp only [CollatzResearch.WordTrace]
  refine ⟨176841839571470057504316761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117894559714313371669544507 176841839571470057504316761)
  ·
    refine ⟨132631379678602543128237571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176841839571470057504316761 132631379678602543128237571)
    ·
      refine ⟨198947069517903814692356357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132631379678602543128237571 198947069517903814692356357)
      ·
        refine ⟨37302575534606965254816817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198947069517903814692356357 37302575534606965254816817)
        ·
          refine ⟨27976931650955223941112613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37302575534606965254816817 27976931650955223941112613)
          ·
            refine ⟨5245674684554104488958615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27976931650955223941112613 5245674684554104488958615)
            ·
              refine ⟨7868512026831156733437923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5245674684554104488958615 7868512026831156733437923)
              ·
                refine ⟨11802768040246735100156885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7868512026831156733437923 11802768040246735100156885)
                ·
                  refine ⟨276627375943282853909927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11802768040246735100156885 276627375943282853909927)
                  ·
                    rfl

theorem cell23_4848569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 7].length) (baseStart_4848569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848569 prefixEnd_4848569 := by exact prefixLift 4848569
  have htrace : WordTrace (prefixWord ++ tailWord_4848569) baseStart_4848569 baseEnd_4848569 := by
    simpa [prefixWord, tailWord_4848569, baseEnd_4848569] using wordTrace_append hprefix tailTrace_4848569
  have hstable : (prefixWord ++ tailWord_4848569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848569).length < 2 ^ (prefixWord ++ tailWord_4848569).sum := by decide
  have hdescent : baseEnd_4848569 < baseStart_4848569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848632 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_4848632 : Nat := 118140960795 + 4848632 * 2 ^ 59
def prefixEnd_4848632 : Nat := 4983230072969 + 3 ^ 40 * 4848632 * 2
def baseEnd_4848632 : Nat := 2489678732770778938701553

theorem tailTrace_4848632 : CollatzResearch.WordTrace tailWord_4848632 prefixEnd_4848632 2489678732770778938701553 := by
  unfold tailWord_4848632
  simp only [CollatzResearch.WordTrace]
  refine ⟨88422068685120909631930075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117896091580161212842573433 88422068685120909631930075)
  ·
    refine ⟨132633103027681364447895113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88422068685120909631930075 132633103027681364447895113)
    ·
      refine ⟨99474827270761023335921335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132633103027681364447895113 99474827270761023335921335)
      ·
        refine ⟨149212240906141535003882003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99474827270761023335921335 149212240906141535003882003)
        ·
          refine ⟨223818361359212302505823005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149212240906141535003882003 223818361359212302505823005)
          ·
            refine ⟨83931885509704613439683627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223818361359212302505823005 83931885509704613439683627)
            ·
              refine ⟨125897828264556920159525441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83931885509704613439683627 125897828264556920159525441)
              ·
                refine ⟨94423371198417690119644081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125897828264556920159525441 94423371198417690119644081)
                ·
                  refine ⟨70817528398813267589733061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94423371198417690119644081 70817528398813267589733061)
                  ·
                    refine ⟨13278286574777487673074949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70817528398813267589733061 13278286574777487673074949)
                    ·
                      refine ⟨2489678732770778938701553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13278286574777487673074949 2489678732770778938701553)
                      ·
                        rfl

theorem cell23_4848632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_4848632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848632 prefixEnd_4848632 := by exact prefixLift 4848632
  have htrace : WordTrace (prefixWord ++ tailWord_4848632) baseStart_4848632 baseEnd_4848632 := by
    simpa [prefixWord, tailWord_4848632, baseEnd_4848632] using wordTrace_append hprefix tailTrace_4848632
  have hstable : (prefixWord ++ tailWord_4848632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848632).length < 2 ^ (prefixWord ++ tailWord_4848632).sum := by decide
  have hdescent : baseEnd_4848632 < baseStart_4848632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848636 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 2, 4, 2]
def baseStart_4848636 : Nat := 118140960795 + 4848636 * 2 ^ 59
def prefixEnd_4848636 : Nat := 4983230072969 + 3 ^ 40 * 4848636 * 2
def baseEnd_4848636 : Nat := 2489680786693396923051535

theorem tailTrace_4848636 : CollatzResearch.WordTrace tailWord_4848636 prefixEnd_4848636 2489680786693396923051535 := by
  unfold tailWord_4848636
  simp only [CollatzResearch.WordTrace]
  refine ⟨88422141631113663973502881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117896188841484885298003841 88422141631113663973502881)
  ·
    refine ⟨66316606223335247980127161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88422141631113663973502881 66316606223335247980127161)
    ·
      refine ⟨49737454667501435985095371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66316606223335247980127161 49737454667501435985095371)
      ·
        refine ⟨74606182001252153977643057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49737454667501435985095371 74606182001252153977643057)
        ·
          refine ⟨55954636500939115483232293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74606182001252153977643057 55954636500939115483232293)
          ·
            refine ⟨10491494343926084153106055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55954636500939115483232293 10491494343926084153106055)
            ·
              refine ⟨15737241515889126229659083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10491494343926084153106055 15737241515889126229659083)
              ·
                refine ⟨23605862273833689344488625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15737241515889126229659083 23605862273833689344488625)
                ·
                  refine ⟨17704396705375267008366469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23605862273833689344488625 17704396705375267008366469)
                  ·
                    refine ⟨3319574382257862564068713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17704396705375267008366469 3319574382257862564068713)
                    ·
                      refine ⟨2489680786693396923051535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3319574382257862564068713 2489680786693396923051535)
                      ·
                        rfl

theorem cell23_4848636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_4848636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848636 prefixEnd_4848636 := by exact prefixLift 4848636
  have htrace : WordTrace (prefixWord ++ tailWord_4848636) baseStart_4848636 baseEnd_4848636 := by
    simpa [prefixWord, tailWord_4848636, baseEnd_4848636] using wordTrace_append hprefix tailTrace_4848636
  have hstable : (prefixWord ++ tailWord_4848636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848636).length < 2 ^ (prefixWord ++ tailWord_4848636).sum := by decide
  have hdescent : baseEnd_4848636 < baseStart_4848636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848663 : List Nat := [1, 1, 3, 5, 1, 1, 1, 5, 1, 4]
def baseStart_4848663 : Nat := 118140960795 + 4848663 * 2 ^ 59
def prefixEnd_4848663 : Nat := 4983230072969 + 3 ^ 40 * 4848663 * 2
def baseEnd_4848663 : Nat := 829898216890356105804637

theorem tailTrace_4848663 : CollatzResearch.WordTrace tailWord_4848663 prefixEnd_4848663 829898216890356105804637 := by
  unfold tailWord_4848663
  simp only [CollatzResearch.WordTrace]
  refine ⟨176845268033129511558238643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117896845355419674372159095 176845268033129511558238643)
  ·
    refine ⟨265267902049694267337357965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176845268033129511558238643 265267902049694267337357965)
    ·
      refine ⟨99475463268635350251509237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265267902049694267337357965 99475463268635350251509237)
      ·
        refine ⟨9325824681434564086078991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99475463268635350251509237 9325824681434564086078991)
        ·
          refine ⟨13988737022151846129118487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9325824681434564086078991 13988737022151846129118487)
          ·
            refine ⟨20983105533227769193677731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13988737022151846129118487 20983105533227769193677731)
            ·
              refine ⟨31474658299841653790516597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20983105533227769193677731 31474658299841653790516597)
              ·
                refine ⟨2950749215610155042860931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31474658299841653790516597 2950749215610155042860931)
                ·
                  refine ⟨4426123823415232564291397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2950749215610155042860931 4426123823415232564291397)
                  ·
                    refine ⟨829898216890356105804637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4426123823415232564291397 829898216890356105804637)
                    ·
                      rfl

theorem cell23_4848663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 1, 4].length) (baseStart_4848663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848663 prefixEnd_4848663 := by exact prefixLift 4848663
  have htrace : WordTrace (prefixWord ++ tailWord_4848663) baseStart_4848663 baseEnd_4848663 := by
    simpa [prefixWord, tailWord_4848663, baseEnd_4848663] using wordTrace_append hprefix tailTrace_4848663
  have hstable : (prefixWord ++ tailWord_4848663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848663).length < 2 ^ (prefixWord ++ tailWord_4848663).sum := by decide
  have hdescent : baseEnd_4848663 < baseStart_4848663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848676 : List Nat := [2, 3, 1, 4, 1, 1, 3, 2, 6]
def baseStart_4848676 : Nat := 118140960795 + 4848676 * 2 ^ 59
def prefixEnd_4848676 : Nat := 4983230072969 + 3 ^ 40 * 4848676 * 2
def baseEnd_4848676 : Nat := 276633480657730751839039

theorem tailTrace_4848676 : CollatzResearch.WordTrace tailWord_4848676 prefixEnd_4848676 276633480657730751839039 := by
  unfold tailWord_4848676
  simp only [CollatzResearch.WordTrace]
  refine ⟨88422871091041207389230941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117897161454721609852307921 88422871091041207389230941)
  ·
    refine ⟨33158576659140452770961603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88422871091041207389230941 33158576659140452770961603)
    ·
      refine ⟨49737864988710679156442405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33158576659140452770961603 49737864988710679156442405)
      ·
        refine ⟨9325849685383252341832951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49737864988710679156442405 9325849685383252341832951)
        ·
          refine ⟨13988774528074878512749427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9325849685383252341832951 13988774528074878512749427)
          ·
            refine ⟨20983161792112317769124141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13988774528074878512749427 20983161792112317769124141)
            ·
              refine ⟨7868685672042119163421553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20983161792112317769124141 7868685672042119163421553)
              ·
                refine ⟨5901514254031589372566165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7868685672042119163421553 5901514254031589372566165)
                ·
                  refine ⟨276633480657730751839039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5901514254031589372566165 276633480657730751839039)
                  ·
                    rfl

theorem cell23_4848676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_4848676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848676 prefixEnd_4848676 := by exact prefixLift 4848676
  have htrace : WordTrace (prefixWord ++ tailWord_4848676) baseStart_4848676 baseEnd_4848676 := by
    simpa [prefixWord, tailWord_4848676, baseEnd_4848676] using wordTrace_append hprefix tailTrace_4848676
  have hstable : (prefixWord ++ tailWord_4848676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848676).length < 2 ^ (prefixWord ++ tailWord_4848676).sum := by decide
  have hdescent : baseEnd_4848676 < baseStart_4848676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848696 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 1, 5, 2]
def baseStart_4848696 : Nat := 118140960795 + 4848696 * 2 ^ 59
def prefixEnd_4848696 : Nat := 4983230072969 + 3 ^ 40 * 4848696 * 2
def baseEnd_4848696 : Nat := 2489711595532666688301259

theorem tailTrace_4848696 : CollatzResearch.WordTrace tailWord_4848696 prefixEnd_4848696 2489711595532666688301259 := by
  unfold tailWord_4848696
  simp only [CollatzResearch.WordTrace]
  refine ⟨88423235821004979097094971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117897647761339972129459961 88423235821004979097094971)
  ·
    refine ⟨132634853731507468645642457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88423235821004979097094971 132634853731507468645642457)
    ·
      refine ⟨99476140298630601484231843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132634853731507468645642457 99476140298630601484231843)
      ·
        refine ⟨149214210447945902226347765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99476140298630601484231843 149214210447945902226347765)
        ·
          refine ⟨13988832229494928333720103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149214210447945902226347765 13988832229494928333720103)
          ·
            refine ⟨20983248344242392500580155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13988832229494928333720103 20983248344242392500580155)
            ·
              refine ⟨31474872516363588750870233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20983248344242392500580155 31474872516363588750870233)
              ·
                refine ⟨23606154387272691563152675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31474872516363588750870233 23606154387272691563152675)
                ·
                  refine ⟨35409231580909037344729013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23606154387272691563152675 35409231580909037344729013)
                  ·
                    refine ⟨3319615460710222251068345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35409231580909037344729013 3319615460710222251068345)
                    ·
                      refine ⟨2489711595532666688301259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3319615460710222251068345 2489711595532666688301259)
                      ·
                        rfl

theorem cell23_4848696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 5, 2].length) (baseStart_4848696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848696 prefixEnd_4848696 := by exact prefixLift 4848696
  have htrace : WordTrace (prefixWord ++ tailWord_4848696) baseStart_4848696 baseEnd_4848696 := by
    simpa [prefixWord, tailWord_4848696, baseEnd_4848696] using wordTrace_append hprefix tailTrace_4848696
  have hstable : (prefixWord ++ tailWord_4848696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848696).length < 2 ^ (prefixWord ++ tailWord_4848696).sum := by decide
  have hdescent : baseEnd_4848696 < baseStart_4848696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848709 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_4848709 : Nat := 118140960795 + 4848709 * 2 ^ 59
def prefixEnd_4848709 : Nat := 4983230072969 + 3 ^ 40 * 4848709 * 2
def baseEnd_4848709 : Nat := 2489718270781175137438699

theorem tailTrace_4848709 : CollatzResearch.WordTrace tailWord_4848709 prefixEnd_4848709 2489718270781175137438699 := by
  unfold tailWord_4848709
  simp only [CollatzResearch.WordTrace]
  refine ⟨176846945790962861414413181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117897963860641907609608787 176846945790962861414413181)
  ·
    refine ⟨66317604671611073030404943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176846945790962861414413181 66317604671611073030404943)
    ·
      refine ⟨99476407007416609545607415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66317604671611073030404943 99476407007416609545607415)
      ·
        refine ⟨149214610511124914318411123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99476407007416609545607415 149214610511124914318411123)
        ·
          refine ⟨223821915766687371477616685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149214610511124914318411123 223821915766687371477616685)
          ·
            refine ⟨83933218412507764304106257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223821915766687371477616685 83933218412507764304106257)
            ·
              refine ⟨62949913809380823228079693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83933218412507764304106257 62949913809380823228079693)
              ·
                refine ⟨23606217678517808710529885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62949913809380823228079693 23606217678517808710529885)
                ·
                  refine ⟨8852331629444178266448707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23606217678517808710529885 8852331629444178266448707)
                  ·
                    refine ⟨13278497444166267399673061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8852331629444178266448707 13278497444166267399673061)
                    ·
                      refine ⟨2489718270781175137438699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13278497444166267399673061 2489718270781175137438699)
                      ·
                        rfl

theorem cell23_4848709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_4848709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848709 prefixEnd_4848709 := by exact prefixLift 4848709
  have htrace : WordTrace (prefixWord ++ tailWord_4848709) baseStart_4848709 baseEnd_4848709 := by
    simpa [prefixWord, tailWord_4848709, baseEnd_4848709] using wordTrace_append hprefix tailTrace_4848709
  have hstable : (prefixWord ++ tailWord_4848709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848709).length < 2 ^ (prefixWord ++ tailWord_4848709).sum := by decide
  have hdescent : baseEnd_4848709 < baseStart_4848709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848736 : List Nat := [2, 1, 1, 3, 2, 2, 2, 4, 2, 4]
def baseStart_4848736 : Nat := 118140960795 + 4848736 * 2 ^ 59
def prefixEnd_4848736 : Nat := 4983230072969 + 3 ^ 40 * 4848736 * 2
def baseEnd_4848736 : Nat := 829910711586282177267025

theorem tailTrace_4848736 : CollatzResearch.WordTrace tailWord_4848736 prefixEnd_4848736 829910711586282177267025 := by
  unfold tailWord_4848736
  simp only [CollatzResearch.WordTrace]
  refine ⟨88423965280932522512823031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117898620374576696683764041 88423965280932522512823031)
  ·
    refine ⟨132635947921398783769234547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88423965280932522512823031 132635947921398783769234547)
    ·
      refine ⟨198953921882098175653851821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132635947921398783769234547 198953921882098175653851821)
      ·
        refine ⟨74607720705786815870194433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198953921882098175653851821 74607720705786815870194433)
        ·
          refine ⟨55955790529340111902645825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74607720705786815870194433 55955790529340111902645825)
          ·
            refine ⟨41966842897005083926984369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55955790529340111902645825 41966842897005083926984369)
            ·
              refine ⟨31475132172753812945238277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41966842897005083926984369 31475132172753812945238277)
              ·
                refine ⟨5901587282391339927232177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31475132172753812945238277 5901587282391339927232177)
                ·
                  refine ⟨4426190461793504945424133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5901587282391339927232177 4426190461793504945424133)
                  ·
                    refine ⟨829910711586282177267025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4426190461793504945424133 829910711586282177267025)
                    ·
                      rfl

theorem cell23_4848736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 2, 4].length) (baseStart_4848736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848736 prefixEnd_4848736 := by exact prefixLift 4848736
  have htrace : WordTrace (prefixWord ++ tailWord_4848736) baseStart_4848736 baseEnd_4848736 := by
    simpa [prefixWord, tailWord_4848736, baseEnd_4848736] using wordTrace_append hprefix tailTrace_4848736
  have hstable : (prefixWord ++ tailWord_4848736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848736).length < 2 ^ (prefixWord ++ tailWord_4848736).sum := by decide
  have hdescent : baseEnd_4848736 < baseStart_4848736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848746 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_4848746 : Nat := 118140960795 + 4848746 * 2 ^ 59
def prefixEnd_4848746 : Nat := 4983230072969 + 3 ^ 40 * 4848746 * 2
def baseEnd_4848746 : Nat := 2489737269565391492676029

theorem tailTrace_4848746 : CollatzResearch.WordTrace tailWord_4848746 prefixEnd_4848746 2489737269565391492676029 := by
  unfold tailWord_4848746
  simp only [CollatzResearch.WordTrace]
  refine ⟨44212073822957204183377523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117898863527885877822340061 44212073822957204183377523)
  ·
    refine ⟨66318110734435806275066285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44212073822957204183377523 66318110734435806275066285)
    ·
      refine ⟨24869291525413427353149857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66318110734435806275066285 24869291525413427353149857)
      ·
        refine ⟨18651968644060070514862393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24869291525413427353149857 18651968644060070514862393)
        ·
          refine ⟨13988976483045052886146795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18651968644060070514862393 13988976483045052886146795)
          ·
            refine ⟨20983464724567579329220193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13988976483045052886146795 20983464724567579329220193)
            ·
              refine ⟨15737598543425684496915145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20983464724567579329220193 15737598543425684496915145)
              ·
                refine ⟨11803198907569263372686359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15737598543425684496915145 11803198907569263372686359)
                ·
                  refine ⟨17704798361353895059029539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11803198907569263372686359 17704798361353895059029539)
                  ·
                    refine ⟨26557197542030842588544309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17704798361353895059029539 26557197542030842588544309)
                    ·
                      refine ⟨2489737269565391492676029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26557197542030842588544309 2489737269565391492676029)
                      ·
                        rfl

theorem cell23_4848746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_4848746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848746 prefixEnd_4848746 := by exact prefixLift 4848746
  have htrace : WordTrace (prefixWord ++ tailWord_4848746) baseStart_4848746 baseEnd_4848746 := by
    simpa [prefixWord, tailWord_4848746, baseEnd_4848746] using wordTrace_append hprefix tailTrace_4848746
  have hstable : (prefixWord ++ tailWord_4848746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848746).length < 2 ^ (prefixWord ++ tailWord_4848746).sum := by decide
  have hdescent : baseEnd_4848746 < baseStart_4848746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848749 : List Nat := [1, 5, 1, 1, 2, 2, 1, 10]
def baseStart_4848749 : Nat := 118140960795 + 4848749 * 2 ^ 59
def prefixEnd_4848749 : Nat := 4983230072969 + 3 ^ 40 * 4848749 * 2
def baseEnd_4848749 : Nat := 92212548518790925219945

theorem tailTrace_4848749 : CollatzResearch.WordTrace tailWord_4848749 prefixEnd_4848749 92212548518790925219945 := by
  unfold tailWord_4848749
  simp only [CollatzResearch.WordTrace]
  refine ⟨176848404710817948245869301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117898936473878632163912867 176848404710817948245869301)
  ·
    refine ⟨16579537941639182648050247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176848404710817948245869301 16579537941639182648050247)
    ·
      refine ⟨24869306912458773972075371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16579537941639182648050247 24869306912458773972075371)
      ·
        refine ⟨37303960368688160958113057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24869306912458773972075371 37303960368688160958113057)
        ·
          refine ⟨27977970276516120718584793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37303960368688160958113057 27977970276516120718584793)
          ·
            refine ⟨20983477707387090538938595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27977970276516120718584793 20983477707387090538938595)
            ·
              refine ⟨31475216561080635808407893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20983477707387090538938595 31475216561080635808407893)
              ·
                refine ⟨92212548518790925219945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31475216561080635808407893 92212548518790925219945)
                ·
                  rfl

theorem cell23_4848749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 10].length) (baseStart_4848749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848749 prefixEnd_4848749 := by exact prefixLift 4848749
  have htrace : WordTrace (prefixWord ++ tailWord_4848749) baseStart_4848749 baseEnd_4848749 := by
    simpa [prefixWord, tailWord_4848749, baseEnd_4848749] using wordTrace_append hprefix tailTrace_4848749
  have hstable : (prefixWord ++ tailWord_4848749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848749).length < 2 ^ (prefixWord ++ tailWord_4848749).sum := by decide
  have hdescent : baseEnd_4848749 < baseStart_4848749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848757 : List Nat := [1, 3, 4, 3, 2, 1, 1, 2, 1, 5]
def baseStart_4848757 : Nat := 118140960795 + 4848757 * 2 ^ 59
def prefixEnd_4848757 : Nat := 4983230072969 + 3 ^ 40 * 4848757 * 2
def baseEnd_4848757 : Nat := 829914305950863649879493

theorem tailTrace_4848757 : CollatzResearch.WordTrace tailWord_4848757 prefixEnd_4848757 829914305950863649879493 := by
  unfold tailWord_4848757
  simp only [CollatzResearch.WordTrace]
  refine ⟨176848696494788965612160525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117899130996525977074773683 176848696494788965612160525)
  ·
    refine ⟨66318261185545862104560197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176848696494788965612160525 66318261185545862104560197)
    ·
      refine ⟨12434673972289849144605037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66318261185545862104560197 12434673972289849144605037)
      ·
        refine ⟨4663002739608693429226889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12434673972289849144605037 4663002739608693429226889)
        ·
          refine ⟨3497252054706520071920167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4663002739608693429226889 3497252054706520071920167)
          ·
            refine ⟨5245878082059780107880251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3497252054706520071920167 5245878082059780107880251)
            ·
              refine ⟨7868817123089670161820377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5245878082059780107880251 7868817123089670161820377)
              ·
                refine ⟨5901612842317252621365283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7868817123089670161820377 5901612842317252621365283)
                ·
                  refine ⟨8852419263475878932047925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5901612842317252621365283 8852419263475878932047925)
                  ·
                    refine ⟨829914305950863649879493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8852419263475878932047925 829914305950863649879493)
                    ·
                      rfl

theorem cell23_4848757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_4848757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848757 prefixEnd_4848757 := by exact prefixLift 4848757
  have htrace : WordTrace (prefixWord ++ tailWord_4848757) baseStart_4848757 baseEnd_4848757 := by
    simpa [prefixWord, tailWord_4848757, baseEnd_4848757] using wordTrace_append hprefix tailTrace_4848757
  have hstable : (prefixWord ++ tailWord_4848757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848757).length < 2 ^ (prefixWord ++ tailWord_4848757).sum := by decide
  have hdescent : baseEnd_4848757 < baseStart_4848757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848794 : List Nat := [3, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2]
def baseStart_4848794 : Nat := 118140960795 + 4848794 * 2 ^ 59
def prefixEnd_4848794 : Nat := 4983230072969 + 3 ^ 40 * 4848794 * 2
def baseEnd_4848794 : Nat := 2489761916636807304875809

theorem tailTrace_4848794 : CollatzResearch.WordTrace tailWord_4848794 prefixEnd_4848794 2489761916636807304875809 := by
  unfold tailWord_4848794
  simp only [CollatzResearch.WordTrace]
  refine ⟨44212511498913730232814359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117900030663769947287504957 44212511498913730232814359)
  ·
    refine ⟨66318767248370595349221539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44212511498913730232814359 66318767248370595349221539)
    ·
      refine ⟨99478150872555893023832309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66318767248370595349221539 99478150872555893023832309)
      ·
        refine ⟨9326076644302114970984279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99478150872555893023832309 9326076644302114970984279)
        ·
          refine ⟨13989114966453172456476419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9326076644302114970984279 13989114966453172456476419)
          ·
            refine ⟨20983672449679758684714629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13989114966453172456476419 20983672449679758684714629)
            ·
              refine ⟨3934438584314954753383993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20983672449679758684714629 3934438584314954753383993)
              ·
                refine ⟨2950828938236216065037995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3934438584314954753383993 2950828938236216065037995)
                ·
                  refine ⟨4426243407354324097556993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2950828938236216065037995 4426243407354324097556993)
                  ·
                    refine ⟨3319682555515743073167745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4426243407354324097556993 3319682555515743073167745)
                    ·
                      refine ⟨2489761916636807304875809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3319682555515743073167745 2489761916636807304875809)
                      ·
                        rfl

theorem cell23_4848794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_4848794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848794 prefixEnd_4848794 := by exact prefixLift 4848794
  have htrace : WordTrace (prefixWord ++ tailWord_4848794) baseStart_4848794 baseEnd_4848794 := by
    simpa [prefixWord, tailWord_4848794, baseEnd_4848794] using wordTrace_append hprefix tailTrace_4848794
  have hstable : (prefixWord ++ tailWord_4848794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848794).length < 2 ^ (prefixWord ++ tailWord_4848794).sum := by decide
  have hdescent : baseEnd_4848794 < baseStart_4848794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848810 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_4848810 : Nat := 118140960795 + 4848810 * 2 ^ 59
def prefixEnd_4848810 : Nat := 4983230072969 + 3 ^ 40 * 4848810 * 2
def baseEnd_4848810 : Nat := 2489770132327279242275735

theorem tailTrace_4848810 : CollatzResearch.WordTrace tailWord_4848810 prefixEnd_4848810 2489770132327279242275735 := by
  unfold tailWord_4848810
  simp only [CollatzResearch.WordTrace]
  refine ⟨44212657390899238915959971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117900419709064637109226589 44212657390899238915959971)
  ·
    refine ⟨66318986086348858373939957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44212657390899238915959971 66318986086348858373939957)
    ·
      refine ⟨6217404945595205472556871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66318986086348858373939957 6217404945595205472556871)
      ·
        refine ⟨9326107418392808208835307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6217404945595205472556871 9326107418392808208835307)
        ·
          refine ⟨13989161127589212313252961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9326107418392808208835307 13989161127589212313252961)
          ·
            refine ⟨10491870845691909234939721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13989161127589212313252961 10491870845691909234939721)
            ·
              refine ⟨7868903134268931926204791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10491870845691909234939721 7868903134268931926204791)
              ·
                refine ⟨11803354701403397889307187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7868903134268931926204791 11803354701403397889307187)
                ·
                  refine ⟨17705032052105096833960781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11803354701403397889307187 17705032052105096833960781)
                  ·
                    refine ⟨6639387019539411312735293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17705032052105096833960781 6639387019539411312735293)
                    ·
                      refine ⟨2489770132327279242275735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6639387019539411312735293 2489770132327279242275735)
                      ·
                        rfl

theorem cell23_4848810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_4848810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848810 prefixEnd_4848810 := by exact prefixLift 4848810
  have htrace : WordTrace (prefixWord ++ tailWord_4848810) baseStart_4848810 baseEnd_4848810 := by
    simpa [prefixWord, tailWord_4848810, baseEnd_4848810] using wordTrace_append hprefix tailTrace_4848810
  have hstable : (prefixWord ++ tailWord_4848810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848810).length < 2 ^ (prefixWord ++ tailWord_4848810).sum := by decide
  have hdescent : baseEnd_4848810 < baseStart_4848810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848816 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 5, 4, 2]
def baseStart_4848816 : Nat := 118140960795 + 4848816 * 2 ^ 59
def prefixEnd_4848816 : Nat := 4983230072969 + 3 ^ 40 * 4848816 * 2
def baseEnd_4848816 : Nat := 2489773213211206218800707

theorem tailTrace_4848816 : CollatzResearch.WordTrace tailWord_4848816 prefixEnd_4848816 2489773213211206218800707 := by
  unfold tailWord_4848816
  simp only [CollatzResearch.WordTrace]
  refine ⟨88425424200787609344279151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117900565601050145792372201 88425424200787609344279151)
  ·
    refine ⟨132638136301181414016418727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88425424200787609344279151 132638136301181414016418727)
    ·
      refine ⟨198957204451772121024628091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132638136301181414016418727 198957204451772121024628091)
      ·
        refine ⟨298435806677658181536942137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198957204451772121024628091 298435806677658181536942137)
        ·
          refine ⟨223826855008243636152706603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298435806677658181536942137 223826855008243636152706603)
          ·
            refine ⟨335740282512365454229059905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223826855008243636152706603 335740282512365454229059905)
            ·
              refine ⟨251805211884274090671794929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335740282512365454229059905 251805211884274090671794929)
              ·
                refine ⟨188853908913205568003846197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251805211884274090671794929 188853908913205568003846197)
                ·
                  refine ⟨17705053960613022000360581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188853908913205568003846197 17705053960613022000360581)
                  ·
                    refine ⟨3319697617614941625067609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17705053960613022000360581 3319697617614941625067609)
                    ·
                      refine ⟨2489773213211206218800707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3319697617614941625067609 2489773213211206218800707)
                      ·
                        rfl

theorem cell23_4848816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 4, 2].length) (baseStart_4848816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848816 prefixEnd_4848816 := by exact prefixLift 4848816
  have htrace : WordTrace (prefixWord ++ tailWord_4848816) baseStart_4848816 baseEnd_4848816 := by
    simpa [prefixWord, tailWord_4848816, baseEnd_4848816] using wordTrace_append hprefix tailTrace_4848816
  have hstable : (prefixWord ++ tailWord_4848816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848816).length < 2 ^ (prefixWord ++ tailWord_4848816).sum := by decide
  have hdescent : baseEnd_4848816 < baseStart_4848816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848819 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 5]
def baseStart_4848819 : Nat := 118140960795 + 4848819 * 2 ^ 59
def prefixEnd_4848819 : Nat := 4983230072969 + 3 ^ 40 * 4848819 * 2
def baseEnd_4848819 : Nat := 2489774753653169707063193

theorem tailTrace_4848819 : CollatzResearch.WordTrace tailWord_4848819 prefixEnd_4848819 2489774753653169707063193 := by
  unfold tailWord_4848819
  simp only [CollatzResearch.WordTrace]
  refine ⟨176850957820564350200917511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117900638547042900133945007 176850957820564350200917511)
  ·
    refine ⟨265276436730846525301376267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176850957820564350200917511 265276436730846525301376267)
    ·
      refine ⟨397914655096269787952064401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265276436730846525301376267 397914655096269787952064401)
      ·
        refine ⟨298435991322202340964048301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397914655096269787952064401 298435991322202340964048301)
        ·
          refine ⟨111913496745825877861518113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 298435991322202340964048301 111913496745825877861518113)
          ·
            refine ⟨83935122559369408396138585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111913496745825877861518113 83935122559369408396138585)
            ·
              refine ⟨62951341919527056297103939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83935122559369408396138585 62951341919527056297103939)
              ·
                refine ⟨94427012879290584445655909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62951341919527056297103939 94427012879290584445655909)
                ·
                  refine ⟨17705064914866984583560483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94427012879290584445655909 17705064914866984583560483)
                  ·
                    refine ⟨26557597372300476875340725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17705064914866984583560483 26557597372300476875340725)
                    ·
                      refine ⟨2489774753653169707063193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26557597372300476875340725 2489774753653169707063193)
                      ·
                        rfl

theorem cell23_4848819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_4848819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848819 prefixEnd_4848819 := by exact prefixLift 4848819
  have htrace : WordTrace (prefixWord ++ tailWord_4848819) baseStart_4848819 baseEnd_4848819 := by
    simpa [prefixWord, tailWord_4848819, baseEnd_4848819] using wordTrace_append hprefix tailTrace_4848819
  have hstable : (prefixWord ++ tailWord_4848819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848819).length < 2 ^ (prefixWord ++ tailWord_4848819).sum := by decide
  have hdescent : baseEnd_4848819 < baseStart_4848819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848850 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_4848850 : Nat := 118140960795 + 4848850 * 2 ^ 59
def prefixEnd_4848850 : Nat := 4983230072969 + 3 ^ 40 * 4848850 * 2
def baseEnd_4848850 : Nat := 2489790671553459085775551

theorem tailTrace_4848850 : CollatzResearch.WordTrace tailWord_4848850 prefixEnd_4848850 2489790671553459085775551 := by
  unfold tailWord_4848850
  simp only [CollatzResearch.WordTrace]
  refine ⟨44213022120863010623824001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117901392322301361663530669 44213022120863010623824001)
  ·
    refine ⟨33159766590647257967868001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44213022120863010623824001 33159766590647257967868001)
    ·
      refine ⟨24869824942985443475901001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33159766590647257967868001 24869824942985443475901001)
      ·
        refine ⟨18652368707239082606925751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24869824942985443475901001 18652368707239082606925751)
        ·
          refine ⟨27978553060858623910388627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18652368707239082606925751 27978553060858623910388627)
          ·
            refine ⟨41967829591287935865582941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27978553060858623910388627 41967829591287935865582941)
            ·
              refine ⟨15737936096732975949593603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41967829591287935865582941 15737936096732975949593603)
              ·
                refine ⟨23606904145099463924390405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15737936096732975949593603 23606904145099463924390405)
                ·
                  refine ⟨4426294527206149485823201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23606904145099463924390405 4426294527206149485823201)
                  ·
                    refine ⟨3319720895404612114367401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4426294527206149485823201 3319720895404612114367401)
                    ·
                      refine ⟨2489790671553459085775551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3319720895404612114367401 2489790671553459085775551)
                      ·
                        rfl

theorem cell23_4848850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_4848850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848850 prefixEnd_4848850 := by exact prefixLift 4848850
  have htrace : WordTrace (prefixWord ++ tailWord_4848850) baseStart_4848850 baseEnd_4848850 := by
    simpa [prefixWord, tailWord_4848850, baseEnd_4848850] using wordTrace_append hprefix tailTrace_4848850
  have hstable : (prefixWord ++ tailWord_4848850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848850).length < 2 ^ (prefixWord ++ tailWord_4848850).sum := by decide
  have hdescent : baseEnd_4848850 < baseStart_4848850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848967 : List Nat := [1, 1, 4, 1, 2, 3, 4, 2, 1, 4]
def baseStart_4848967 : Nat := 118140960795 + 4848967 * 2 ^ 59
def prefixEnd_4848967 : Nat := 4983230072969 + 3 ^ 40 * 4848967 * 2
def baseEnd_4848967 : Nat := 829950249596678376004171

theorem tailTrace_4848967 : CollatzResearch.WordTrace tailWord_4848967 prefixEnd_4848967 829950249596678376004171 := by
  unfold tailWord_4848967
  simp only [CollatzResearch.WordTrace]
  refine ⟨176856355824028171477305155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117904237216018780984870103 176856355824028171477305155)
  ·
    refine ⟨265284533736042257215957733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176856355824028171477305155 265284533736042257215957733)
    ·
      refine ⟨49740850075507923227992075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265284533736042257215957733 49740850075507923227992075)
      ·
        refine ⟨74611275113261884841988113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49740850075507923227992075 74611275113261884841988113)
        ·
          refine ⟨55958456334946413631491085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74611275113261884841988113 55958456334946413631491085)
          ·
            refine ⟨20984421125604905111809157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55958456334946413631491085 20984421125604905111809157)
            ·
              refine ⟨3934578961050919708464217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20984421125604905111809157 3934578961050919708464217)
              ·
                refine ⟨2950934220788189781348163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3934578961050919708464217 2950934220788189781348163)
                ·
                  refine ⟨4426401331182284672022245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2950934220788189781348163 4426401331182284672022245)
                  ·
                    refine ⟨829950249596678376004171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4426401331182284672022245 829950249596678376004171)
                    ·
                      rfl

theorem cell23_4848967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_4848967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848967 prefixEnd_4848967 := by exact prefixLift 4848967
  have htrace : WordTrace (prefixWord ++ tailWord_4848967) baseStart_4848967 baseEnd_4848967 := by
    simpa [prefixWord, tailWord_4848967, baseEnd_4848967] using wordTrace_append hprefix tailTrace_4848967
  have hstable : (prefixWord ++ tailWord_4848967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848967).length < 2 ^ (prefixWord ++ tailWord_4848967).sum := by decide
  have hdescent : baseEnd_4848967 < baseStart_4848967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4848976 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 5, 5]
def baseStart_4848976 : Nat := 118140960795 + 4848976 * 2 ^ 59
def prefixEnd_4848976 : Nat := 4983230072969 + 3 ^ 40 * 4848976 * 2
def baseEnd_4848976 : Nat := 829951790038641864266657

theorem tailTrace_4848976 : CollatzResearch.WordTrace tailWord_4848976 prefixEnd_4848976 829951790038641864266657 := by
  unfold tailWord_4848976
  simp only [CollatzResearch.WordTrace]
  refine ⟨88428342040497783007191391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117904456053997044009588521 88428342040497783007191391)
  ·
    refine ⟨132642513060746674510787087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88428342040497783007191391 132642513060746674510787087)
    ·
      refine ⟨198963769591120011766180631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132642513060746674510787087 198963769591120011766180631)
      ·
        refine ⟨298445654386680017649270947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198963769591120011766180631 298445654386680017649270947)
        ·
          refine ⟨447668481580020026473906421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298445654386680017649270947 447668481580020026473906421)
          ·
            refine ⟨41968920148126877481928727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 447668481580020026473906421 41968920148126877481928727)
            ·
              refine ⟨62953380222190316222893091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41968920148126877481928727 62953380222190316222893091)
              ·
                refine ⟨94430070333285474334339637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62953380222190316222893091 94430070333285474334339637)
                ·
                  refine ⟨8852819093745513218844341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94430070333285474334339637 8852819093745513218844341)
                  ·
                    refine ⟨829951790038641864266657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8852819093745513218844341 829951790038641864266657)
                    ·
                      rfl

theorem cell23_4848976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5, 5].length) (baseStart_4848976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4848976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4848976 prefixEnd_4848976 := by exact prefixLift 4848976
  have htrace : WordTrace (prefixWord ++ tailWord_4848976) baseStart_4848976 baseEnd_4848976 := by
    simpa [prefixWord, tailWord_4848976, baseEnd_4848976] using wordTrace_append hprefix tailTrace_4848976
  have hstable : (prefixWord ++ tailWord_4848976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4848976).length < 2 ^ (prefixWord ++ tailWord_4848976).sum := by decide
  have hdescent : baseEnd_4848976 < baseStart_4848976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4848976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849007 : List Nat := [1, 1, 2, 1, 3, 1, 6, 3, 1, 1, 3]
def baseStart_4849007 : Nat := 118140960795 + 4849007 * 2 ^ 59
def prefixEnd_4849007 : Nat := 4983230072969 + 3 ^ 40 * 4849007 * 2
def baseEnd_4849007 : Nat := 2489871288016214971512329

theorem tailTrace_4849007 : CollatzResearch.WordTrace tailWord_4849007 prefixEnd_4849007 2489871288016214971512329 := by
  unfold tailWord_4849007
  simp only [CollatzResearch.WordTrace]
  refine ⟨176857814743883258308761275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117905209829255505539174183 176857814743883258308761275)
  ·
    refine ⟨265286722115824887463141913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176857814743883258308761275 265286722115824887463141913)
    ·
      refine ⟨198965041586868665597356435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265286722115824887463141913 198965041586868665597356435)
      ·
        refine ⟨298447562380302998396034653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198965041586868665597356435 298447562380302998396034653)
        ·
          refine ⟨111917835892613624398512995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 298447562380302998396034653 111917835892613624398512995)
          ·
            refine ⟨167876753838920436597769493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111917835892613624398512995 167876753838920436597769493)
            ·
              refine ⟨7869222836199395465520445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 167876753838920436597769493 7869222836199395465520445)
              ·
                refine ⟨2950958563574773299570167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7869222836199395465520445 2950958563574773299570167)
                ·
                  refine ⟨4426437845362159949355251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2950958563574773299570167 4426437845362159949355251)
                  ·
                    refine ⟨6639656768043239924032877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4426437845362159949355251 6639656768043239924032877)
                    ·
                      refine ⟨2489871288016214971512329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6639656768043239924032877 2489871288016214971512329)
                      ·
                        rfl

theorem cell23_4849007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 1, 1, 3].length) (baseStart_4849007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849007 prefixEnd_4849007 := by exact prefixLift 4849007
  have htrace : WordTrace (prefixWord ++ tailWord_4849007) baseStart_4849007 baseEnd_4849007 := by
    simpa [prefixWord, tailWord_4849007, baseEnd_4849007] using wordTrace_append hprefix tailTrace_4849007
  have hstable : (prefixWord ++ tailWord_4849007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849007).length < 2 ^ (prefixWord ++ tailWord_4849007).sum := by decide
  have hdescent : baseEnd_4849007 < baseStart_4849007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849016 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_4849016 : Nat := 118140960795 + 4849016 * 2 ^ 59
def prefixEnd_4849016 : Nat := 4983230072969 + 3 ^ 40 * 4849016 * 2
def baseEnd_4849016 : Nat := 2489875909342105436299787

theorem tailTrace_4849016 : CollatzResearch.WordTrace tailWord_4849016 prefixEnd_4849016 2489875909342105436299787 := by
  unfold tailWord_4849016
  simp only [CollatzResearch.WordTrace]
  refine ⟨88429071500425326422919451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117905428667233768563892601 88429071500425326422919451)
  ·
    refine ⟨132643607250637989634379177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88429071500425326422919451 132643607250637989634379177)
    ·
      refine ⟨99482705437978492225784383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132643607250637989634379177 99482705437978492225784383)
      ·
        refine ⟨149224058156967738338676575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99482705437978492225784383 149224058156967738338676575)
        ·
          refine ⟨223836087235451607508014863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149224058156967738338676575 223836087235451607508014863)
          ·
            refine ⟨335754130853177411262022295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223836087235451607508014863 335754130853177411262022295)
            ·
              refine ⟨503631196279766116893033443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335754130853177411262022295 503631196279766116893033443)
              ·
                refine ⟨755446794419649175339550165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503631196279766116893033443 755446794419649175339550165)
                ·
                  refine ⟨17705784244210527547020707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 755446794419649175339550165 17705784244210527547020707)
                  ·
                    refine ⟨26558676366315791320531061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17705784244210527547020707 26558676366315791320531061)
                    ·
                      refine ⟨2489875909342105436299787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26558676366315791320531061 2489875909342105436299787)
                      ·
                        rfl

theorem cell23_4849016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_4849016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849016 prefixEnd_4849016 := by exact prefixLift 4849016
  have htrace : WordTrace (prefixWord ++ tailWord_4849016) baseStart_4849016 baseEnd_4849016 := by
    simpa [prefixWord, tailWord_4849016, baseEnd_4849016] using wordTrace_append hprefix tailTrace_4849016
  have hstable : (prefixWord ++ tailWord_4849016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849016).length < 2 ^ (prefixWord ++ tailWord_4849016).sum := by decide
  have hdescent : baseEnd_4849016 < baseStart_4849016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849036 : List Nat := [2, 2, 1, 2, 1, 3, 2, 10]
def baseStart_4849036 : Nat := 118140960795 + 4849036 * 2 ^ 59
def prefixEnd_4849036 : Nat := 4983230072969 + 3 ^ 40 * 4849036 * 2
def baseEnd_4849036 : Nat := 92218006627970198446285

theorem tailTrace_4849036 : CollatzResearch.WordTrace tailWord_4849036 prefixEnd_4849036 92218006627970198446285 := by
  unfold tailWord_4849036
  simp only [CollatzResearch.WordTrace]
  refine ⟨88429436230389098130783481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117905914973852130841044641 88429436230389098130783481)
  ·
    refine ⟨66322077172791823598087611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88429436230389098130783481 66322077172791823598087611)
    ·
      refine ⟨99483115759187735397131417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66322077172791823598087611 99483115759187735397131417)
      ·
        refine ⟨74612336819390801547848563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99483115759187735397131417 74612336819390801547848563)
        ·
          refine ⟨111918505229086202321772845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74612336819390801547848563 111918505229086202321772845)
          ·
            refine ⟨41969439460907325870664817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111918505229086202321772845 41969439460907325870664817)
            ·
              refine ⟨31477079595680494402998613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41969439460907325870664817 31477079595680494402998613)
              ·
                refine ⟨92218006627970198446285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31477079595680494402998613 92218006627970198446285)
                ·
                  rfl

theorem cell23_4849036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 10].length) (baseStart_4849036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849036 prefixEnd_4849036 := by exact prefixLift 4849036
  have htrace : WordTrace (prefixWord ++ tailWord_4849036) baseStart_4849036 baseEnd_4849036 := by
    simpa [prefixWord, tailWord_4849036, baseEnd_4849036] using wordTrace_append hprefix tailTrace_4849036
  have hstable : (prefixWord ++ tailWord_4849036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849036).length < 2 ^ (prefixWord ++ tailWord_4849036).sum := by decide
  have hdescent : baseEnd_4849036 < baseStart_4849036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849053 : List Nat := [1, 4, 2, 1, 3, 2, 1, 9]
def baseStart_4849053 : Nat := 118140960795 + 4849053 * 2 ^ 59
def prefixEnd_4849053 : Nat := 4983230072969 + 3 ^ 40 * 4849053 * 2
def baseEnd_4849053 : Nat := 92218329930604510797671

theorem tailTrace_4849053 : CollatzResearch.WordTrace tailWord_4849053 prefixEnd_4849053 92218329930604510797671 := by
  unfold tailWord_4849053
  simp only [CollatzResearch.WordTrace]
  refine ⟨176859492501716608164935813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117906328334477738776623875 176859492501716608164935813)
  ·
    refine ⟨33161154844071864030925465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176859492501716608164935813 33161154844071864030925465)
    ·
      refine ⟨24870866133053898023194099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33161154844071864030925465 24870866133053898023194099)
      ·
        refine ⟨37306299199580847034791149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24870866133053898023194099 37306299199580847034791149)
        ·
          refine ⟨13989862199842817638046681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37306299199580847034791149 13989862199842817638046681)
          ·
            refine ⟨10492396649882113228535011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13989862199842817638046681 10492396649882113228535011)
            ·
              refine ⟨15738594974823169842802517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10492396649882113228535011 15738594974823169842802517)
              ·
                refine ⟨92218329930604510797671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15738594974823169842802517 92218329930604510797671)
                ·
                  rfl

theorem cell23_4849053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 9].length) (baseStart_4849053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849053 prefixEnd_4849053 := by exact prefixLift 4849053
  have htrace : WordTrace (prefixWord ++ tailWord_4849053) baseStart_4849053 baseEnd_4849053 := by
    simpa [prefixWord, tailWord_4849053, baseEnd_4849053] using wordTrace_append hprefix tailTrace_4849053
  have hstable : (prefixWord ++ tailWord_4849053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849053).length < 2 ^ (prefixWord ++ tailWord_4849053).sum := by decide
  have hdescent : baseEnd_4849053 < baseStart_4849053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849080 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 4, 1, 3]
def baseStart_4849080 : Nat := 118140960795 + 4849080 * 2 ^ 59
def prefixEnd_4849080 : Nat := 4983230072969 + 3 ^ 40 * 4849080 * 2
def baseEnd_4849080 : Nat := 2489908772103993185899493

theorem tailTrace_4849080 : CollatzResearch.WordTrace tailWord_4849080 prefixEnd_4849080 2489908772103993185899493 := by
  unfold tailWord_4849080
  simp only [CollatzResearch.WordTrace]
  refine ⟨88430238636309395888084347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117906984848412527850779129 88430238636309395888084347)
  ·
    refine ⟨132645357954464093832126521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88430238636309395888084347 132645357954464093832126521)
    ·
      refine ⟨99484018465848070374094891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132645357954464093832126521 99484018465848070374094891)
      ·
        refine ⟨149226027698772105561142337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99484018465848070374094891 149226027698772105561142337)
        ·
          refine ⟨111919520774079079170856753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149226027698772105561142337 111919520774079079170856753)
          ·
            refine ⟨83939640580559309378142565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111919520774079079170856753 83939640580559309378142565)
            ·
              refine ⟨15738682608854870508401731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83939640580559309378142565 15738682608854870508401731)
              ·
                refine ⟨23608023913282305762602597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15738682608854870508401731 23608023913282305762602597)
                ·
                  refine ⟨4426504483740432330487987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23608023913282305762602597 4426504483740432330487987)
                  ·
                    refine ⟨6639756725610648495731981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4426504483740432330487987 6639756725610648495731981)
                    ·
                      refine ⟨2489908772103993185899493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6639756725610648495731981 2489908772103993185899493)
                      ·
                        rfl

theorem cell23_4849080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_4849080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849080 prefixEnd_4849080 := by exact prefixLift 4849080
  have htrace : WordTrace (prefixWord ++ tailWord_4849080) baseStart_4849080 baseEnd_4849080 := by
    simpa [prefixWord, tailWord_4849080, baseEnd_4849080] using wordTrace_append hprefix tailTrace_4849080
  have hstable : (prefixWord ++ tailWord_4849080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849080).length < 2 ^ (prefixWord ++ tailWord_4849080).sum := by decide
  have hdescent : baseEnd_4849080 < baseStart_4849080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849081 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 3, 2, 2]
def baseStart_4849081 : Nat := 118140960795 + 4849081 * 2 ^ 59
def prefixEnd_4849081 : Nat := 4983230072969 + 3 ^ 40 * 4849081 * 2
def baseEnd_4849081 : Nat := 2489909285584647681986989

theorem tailTrace_4849081 : CollatzResearch.WordTrace tailWord_4849081 prefixEnd_4849081 2489909285584647681986989 := by
  unfold tailWord_4849081
  simp only [CollatzResearch.WordTrace]
  refine ⟨176860513745615168946955097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117907009163743445964636731 176860513745615168946955097)
  ·
    refine ⟨132645385309211376710216323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176860513745615168946955097 132645385309211376710216323)
    ·
      refine ⟨198968077963817065065324485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132645385309211376710216323 198968077963817065065324485)
      ·
        refine ⟨37306514618215699699748341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198968077963817065065324485 37306514618215699699748341)
        ·
          refine ⟨3497485745457721846851407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37306514618215699699748341 3497485745457721846851407)
          ·
            refine ⟨5246228618186582770277111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3497485745457721846851407 5246228618186582770277111)
            ·
              refine ⟨7869342927279874155415667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5246228618186582770277111 7869342927279874155415667)
              ·
                refine ⟨11804014390919811233123501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7869342927279874155415667 11804014390919811233123501)
                ·
                  refine ⟨4426505396594929212421313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11804014390919811233123501 4426505396594929212421313)
                  ·
                    refine ⟨3319879047446196909315985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4426505396594929212421313 3319879047446196909315985)
                    ·
                      refine ⟨2489909285584647681986989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3319879047446196909315985 2489909285584647681986989)
                      ·
                        rfl

theorem cell23_4849081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_4849081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849081 prefixEnd_4849081 := by exact prefixLift 4849081
  have htrace : WordTrace (prefixWord ++ tailWord_4849081) baseStart_4849081 baseEnd_4849081 := by
    simpa [prefixWord, tailWord_4849081, baseEnd_4849081] using wordTrace_append hprefix tailTrace_4849081
  have hstable : (prefixWord ++ tailWord_4849081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849081).length < 2 ^ (prefixWord ++ tailWord_4849081).sum := by decide
  have hdescent : baseEnd_4849081 < baseStart_4849081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849154 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_4849154 : Nat := 118140960795 + 4849154 * 2 ^ 59
def prefixEnd_4849154 : Nat := 4983230072969 + 3 ^ 40 * 4849154 * 2
def baseEnd_4849154 : Nat := 2489946769672425896374153

theorem tailTrace_4849154 : CollatzResearch.WordTrace tailWord_4849154 prefixEnd_4849154 2489946769672425896374153 := by
  unfold tailWord_4849154
  simp only [CollatzResearch.WordTrace]
  refine ⟨44215794068587675603590629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117908784182900468276241677 44215794068587675603590629)
  ·
    refine ⟨8290461387860189175673243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44215794068587675603590629 8290461387860189175673243)
    ·
      refine ⟨12435692081790283763509865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8290461387860189175673243 12435692081790283763509865)
      ·
        refine ⟨9326769061342712822632399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12435692081790283763509865 9326769061342712822632399)
        ·
          refine ⟨13990153592014069233948599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9326769061342712822632399 13990153592014069233948599)
          ·
            refine ⟨20985230388021103850922899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13990153592014069233948599 20985230388021103850922899)
            ·
              refine ⟨31477845582031655776384349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20985230388021103850922899 31477845582031655776384349)
              ·
                refine ⟨11804192093261870916144131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31477845582031655776384349 11804192093261870916144131)
                ·
                  refine ⟨17706288139892806374216197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11804192093261870916144131 17706288139892806374216197)
                  ·
                    refine ⟨3319929026229901195165537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17706288139892806374216197 3319929026229901195165537)
                    ·
                      refine ⟨2489946769672425896374153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3319929026229901195165537 2489946769672425896374153)
                      ·
                        rfl

theorem cell23_4849154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_4849154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849154 prefixEnd_4849154 := by exact prefixLift 4849154
  have htrace : WordTrace (prefixWord ++ tailWord_4849154) baseStart_4849154 baseEnd_4849154 := by
    simpa [prefixWord, tailWord_4849154, baseEnd_4849154] using wordTrace_append hprefix tailTrace_4849154
  have hstable : (prefixWord ++ tailWord_4849154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849154).length < 2 ^ (prefixWord ++ tailWord_4849154).sum := by decide
  have hdescent : baseEnd_4849154 < baseStart_4849154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849182 : List Nat := [4, 3, 3, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4849182 : Nat := 118140960795 + 4849182 * 2 ^ 59
def prefixEnd_4849182 : Nat := 4983230072969 + 3 ^ 40 * 4849182 * 2
def baseEnd_4849182 : Nat := 2489961147130751786824025

theorem tailTrace_4849182 : CollatzResearch.WordTrace tailWord_4849182 prefixEnd_4849182 2489961147130751786824025 := by
  unfold tailWord_4849182
  simp only [CollatzResearch.WordTrace]
  refine ⟨22108024689781157899547725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117909465012166175464254533 22108024689781157899547725)
  ·
    refine ⟨8290509258667934212330397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22108024689781157899547725 8290509258667934212330397)
    ·
      refine ⟨3108940972000475329623899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8290509258667934212330397 3108940972000475329623899)
      ·
        refine ⟨4663411458000712994435849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3108940972000475329623899 4663411458000712994435849)
        ·
          refine ⟨3497558593500534745826887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4663411458000712994435849 3497558593500534745826887)
          ·
            refine ⟨5246337890250802118740331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3497558593500534745826887 5246337890250802118740331)
            ·
              refine ⟨7869506835376203178110497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5246337890250802118740331 7869506835376203178110497)
              ·
                refine ⟨5902130126532152383582873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7869506835376203178110497 5902130126532152383582873)
                ·
                  refine ⟨4426597594899114287687155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5902130126532152383582873 4426597594899114287687155)
                  ·
                    refine ⟨6639896392348671431530733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4426597594899114287687155 6639896392348671431530733)
                    ·
                      refine ⟨2489961147130751786824025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6639896392348671431530733 2489961147130751786824025)
                      ·
                        rfl

theorem cell23_4849182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4849182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849182 prefixEnd_4849182 := by exact prefixLift 4849182
  have htrace : WordTrace (prefixWord ++ tailWord_4849182) baseStart_4849182 baseEnd_4849182 := by
    simpa [prefixWord, tailWord_4849182, baseEnd_4849182] using wordTrace_append hprefix tailTrace_4849182
  have hstable : (prefixWord ++ tailWord_4849182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849182).length < 2 ^ (prefixWord ++ tailWord_4849182).sum := by decide
  have hdescent : baseEnd_4849182 < baseStart_4849182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849183 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 5]
def baseStart_4849183 : Nat := 118140960795 + 4849183 * 2 ^ 59
def prefixEnd_4849183 : Nat := 4983230072969 + 3 ^ 40 * 4849183 * 2
def baseEnd_4849183 : Nat := 2489961660611406282911519

theorem tailTrace_4849183 : CollatzResearch.WordTrace tailWord_4849183 prefixEnd_4849183 2489961660611406282911519 := by
  unfold tailWord_4849183
  simp only [CollatzResearch.WordTrace]
  refine ⟨176864233991245640367168203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117909489327497093578112135 176864233991245640367168203)
  ·
    refine ⟨265296350986868460550752305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176864233991245640367168203 265296350986868460550752305)
    ·
      refine ⟨198972263240151345413064229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265296350986868460550752305 198972263240151345413064229)
      ·
        refine ⟨37307299357528377264949543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198972263240151345413064229 37307299357528377264949543)
        ·
          refine ⟨55960949036292565897424315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37307299357528377264949543 55960949036292565897424315)
          ·
            refine ⟨83941423554438848846136473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55960949036292565897424315 83941423554438848846136473)
            ·
              refine ⟨62956067665829136634602355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83941423554438848846136473 62956067665829136634602355)
              ·
                refine ⟨94434101498743704951903533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62956067665829136634602355 94434101498743704951903533)
                ·
                  refine ⟨35412788062028889356963825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94434101498743704951903533 35412788062028889356963825)
                  ·
                    refine ⟨26559591046521667017722869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35412788062028889356963825 26559591046521667017722869)
                    ·
                      refine ⟨2489961660611406282911519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26559591046521667017722869 2489961660611406282911519)
                      ·
                        rfl

theorem cell23_4849183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_4849183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849183 prefixEnd_4849183 := by exact prefixLift 4849183
  have htrace : WordTrace (prefixWord ++ tailWord_4849183) baseStart_4849183 baseEnd_4849183 := by
    simpa [prefixWord, tailWord_4849183, baseEnd_4849183] using wordTrace_append hprefix tailTrace_4849183
  have hstable : (prefixWord ++ tailWord_4849183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849183).length < 2 ^ (prefixWord ++ tailWord_4849183).sum := by decide
  have hdescent : baseEnd_4849183 < baseStart_4849183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849233 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 10]
def baseStart_4849233 : Nat := 118140960795 + 4849233 * 2 ^ 59
def prefixEnd_4849233 : Nat := 4983230072969 + 3 ^ 40 * 4849233 * 2
def baseEnd_4849233 : Nat := 276665259404903454142921

theorem tailTrace_4849233 : CollatzResearch.WordTrace tailWord_4849233 prefixEnd_4849233 276665259404903454142921 := by
  unfold tailWord_4849233
  simp only [CollatzResearch.WordTrace]
  refine ⟨176866057641064498906488353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117910705094042999270992235 176866057641064498906488353)
  ·
    refine ⟨132649543230798374179866265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176866057641064498906488353 132649543230798374179866265)
    ·
      refine ⟨99487157423098780634899699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132649543230798374179866265 99487157423098780634899699)
      ·
        refine ⟨149230736134648170952349549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99487157423098780634899699 149230736134648170952349549)
        ·
          refine ⟨55961526050493064107131081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149230736134648170952349549 55961526050493064107131081)
          ·
            refine ⟨41971144537869798080348311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55961526050493064107131081 41971144537869798080348311)
            ·
              refine ⟨62956716806804697120522467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41971144537869798080348311 62956716806804697120522467)
              ·
                refine ⟨94435075210207045680783701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62956716806804697120522467 94435075210207045680783701)
                ·
                  refine ⟨276665259404903454142921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 94435075210207045680783701 276665259404903454142921)
                  ·
                    rfl

theorem cell23_4849233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 10].length) (baseStart_4849233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849233 prefixEnd_4849233 := by exact prefixLift 4849233
  have htrace : WordTrace (prefixWord ++ tailWord_4849233) baseStart_4849233 baseEnd_4849233 := by
    simpa [prefixWord, tailWord_4849233, baseEnd_4849233] using wordTrace_append hprefix tailTrace_4849233
  have hstable : (prefixWord ++ tailWord_4849233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849233).length < 2 ^ (prefixWord ++ tailWord_4849233).sum := by decide
  have hdescent : baseEnd_4849233 < baseStart_4849233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849263 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 2, 9]
def baseStart_4849263 : Nat := 118140960795 + 4849263 * 2 ^ 59
def prefixEnd_4849263 : Nat := 4983230072969 + 3 ^ 40 * 4849263 * 2
def baseEnd_4849263 : Nat := 830000913021255323303717

theorem tailTrace_4849263 : CollatzResearch.WordTrace tailWord_4849263 prefixEnd_4849263 830000913021255323303717 := by
  unfold tailWord_4849263
  simp only [CollatzResearch.WordTrace]
  refine ⟨176867151830955814030080443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117911434553970542686720295 176867151830955814030080443)
  ·
    refine ⟨265300727746433721045120665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176867151830955814030080443 265300727746433721045120665)
    ·
      refine ⟨198975545809825290783840499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265300727746433721045120665 198975545809825290783840499)
      ·
        refine ⟨298463318714737936175760749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198975545809825290783840499 298463318714737936175760749)
        ·
          refine ⟨111923744518026726065910281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 298463318714737936175760749 111923744518026726065910281)
          ·
            refine ⟨83942808388520044549432711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111923744518026726065910281 83942808388520044549432711)
            ·
              refine ⟨125914212582780066824149067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83942808388520044549432711 125914212582780066824149067)
              ·
                refine ⟨188871318874170100236223601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125914212582780066824149067 188871318874170100236223601)
                ·
                  refine ⟨141653489155627575177167701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188871318874170100236223601 141653489155627575177167701)
                  ·
                    refine ⟨830000913021255323303717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 141653489155627575177167701 830000913021255323303717)
                    ·
                      rfl

theorem cell23_4849263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_4849263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849263 prefixEnd_4849263 := by exact prefixLift 4849263
  have htrace : WordTrace (prefixWord ++ tailWord_4849263) baseStart_4849263 baseEnd_4849263 := by
    simpa [prefixWord, tailWord_4849263, baseEnd_4849263] using wordTrace_append hprefix tailTrace_4849263
  have hstable : (prefixWord ++ tailWord_4849263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849263).length < 2 ^ (prefixWord ++ tailWord_4849263).sum := by decide
  have hdescent : baseEnd_4849263 < baseStart_4849263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849280 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 3, 5]
def baseStart_4849280 : Nat := 118140960795 + 4849280 * 2 ^ 59
def prefixEnd_4849280 : Nat := 4983230072969 + 3 ^ 40 * 4849280 * 2
def baseEnd_4849280 : Nat := 830003822744964134466191

theorem tailTrace_4849280 : CollatzResearch.WordTrace tailWord_4849280 prefixEnd_4849280 830003822744964134466191 := by
  unfold tailWord_4849280
  simp only [CollatzResearch.WordTrace]
  refine ⟨88433885935947112966724647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117911847914596150622299529 88433885935947112966724647)
  ·
    refine ⟨132650828903920669450086971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88433885935947112966724647 132650828903920669450086971)
    ·
      refine ⟨198976243355881004175130457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132650828903920669450086971 198976243355881004175130457)
      ·
        refine ⟨149232182516910753131347843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198976243355881004175130457 149232182516910753131347843)
        ·
          refine ⟨223848273775366129697021765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149232182516910753131347843 223848273775366129697021765)
          ·
            refine ⟨41971551332881149318191581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 223848273775366129697021765 41971551332881149318191581)
            ·
              refine ⟨15739331749830430994321843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41971551332881149318191581 15739331749830430994321843)
              ·
                refine ⟨23608997624745646491482765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15739331749830430994321843 23608997624745646491482765)
                ·
                  refine ⟨8853374109279617434306037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23608997624745646491482765 8853374109279617434306037)
                  ·
                    refine ⟨830003822744964134466191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8853374109279617434306037 830003822744964134466191)
                    ·
                      rfl

theorem cell23_4849280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3, 5].length) (baseStart_4849280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849280 prefixEnd_4849280 := by exact prefixLift 4849280
  have htrace : WordTrace (prefixWord ++ tailWord_4849280) baseStart_4849280 baseEnd_4849280 := by
    simpa [prefixWord, tailWord_4849280, baseEnd_4849280] using wordTrace_append hprefix tailTrace_4849280
  have hstable : (prefixWord ++ tailWord_4849280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849280).length < 2 ^ (prefixWord ++ tailWord_4849280).sum := by decide
  have hdescent : baseEnd_4849280 < baseStart_4849280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849304 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 2, 3, 2]
def baseStart_4849304 : Nat := 118140960795 + 4849304 * 2 ^ 59
def prefixEnd_4849304 : Nat := 4983230072969 + 3 ^ 40 * 4849304 * 2
def baseEnd_4849304 : Nat := 2490023791770600309498463

theorem tailTrace_4849304 : CollatzResearch.WordTrace tailWord_4849304 prefixEnd_4849304 2490023791770600309498463 := by
  unfold tailWord_4849304
  simp only [CollatzResearch.WordTrace]
  refine ⟨88434323611903639016161483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117912431482538185354881977 88434323611903639016161483)
  ·
    refine ⟨132651485417855458524242225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88434323611903639016161483 132651485417855458524242225)
    ·
      refine ⟨99488614063391593893181669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132651485417855458524242225 99488614063391593893181669)
      ·
        refine ⟨18654115136885923854971563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99488614063391593893181669 18654115136885923854971563)
        ·
          refine ⟨27981172705328885782457345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18654115136885923854971563 27981172705328885782457345)
          ·
            refine ⟨20985879528996664336843009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27981172705328885782457345 20985879528996664336843009)
            ·
              refine ⟨15739409646747498252632257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20985879528996664336843009 15739409646747498252632257)
              ·
                refine ⟨11804557235060623689474193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15739409646747498252632257 11804557235060623689474193)
                ·
                  refine ⟨8853417926295467767105645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11804557235060623689474193 8853417926295467767105645)
                  ·
                    refine ⟨3320031722360800412664617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8853417926295467767105645 3320031722360800412664617)
                    ·
                      refine ⟨2490023791770600309498463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3320031722360800412664617 2490023791770600309498463)
                      ·
                        rfl

theorem cell23_4849304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_4849304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849304 prefixEnd_4849304 := by exact prefixLift 4849304
  have htrace : WordTrace (prefixWord ++ tailWord_4849304) baseStart_4849304 baseEnd_4849304 := by
    simpa [prefixWord, tailWord_4849304, baseEnd_4849304] using wordTrace_append hprefix tailTrace_4849304
  have hstable : (prefixWord ++ tailWord_4849304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849304).length < 2 ^ (prefixWord ++ tailWord_4849304).sum := by decide
  have hdescent : baseEnd_4849304 < baseStart_4849304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849327 : List Nat := [1, 1, 2, 1, 2, 4, 1, 5, 2, 4]
def baseStart_4849327 : Nat := 118140960795 + 4849327 * 2 ^ 59
def prefixEnd_4849327 : Nat := 4983230072969 + 3 ^ 40 * 4849327 * 2
def baseEnd_4849327 : Nat := 830011867275217906503619

theorem tailTrace_4849327 : CollatzResearch.WordTrace tailWord_4849327 prefixEnd_4849327 830011867275217906503619 := by
  unfold tailWord_4849327
  simp only [CollatzResearch.WordTrace]
  refine ⟨176869486102723952960410235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117912990735149301973606823 176869486102723952960410235)
  ·
    refine ⟨265304229154085929440615353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176869486102723952960410235 265304229154085929440615353)
    ·
      refine ⟨198978171865564447080461515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265304229154085929440615353 198978171865564447080461515)
      ·
        refine ⟨298467257798346670620692273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198978171865564447080461515 298467257798346670620692273)
        ·
          refine ⟨223850443348760002965519205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298467257798346670620692273 223850443348760002965519205)
          ·
            refine ⟨41971958127892500556034851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 223850443348760002965519205 41971958127892500556034851)
            ·
              refine ⟨62957937191838750834052277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41971958127892500556034851 62957937191838750834052277)
              ·
                refine ⟨5902306611734882890692401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62957937191838750834052277 5902306611734882890692401)
                ·
                  refine ⟨4426729958801162168019301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5902306611734882890692401 4426729958801162168019301)
                  ·
                    refine ⟨830011867275217906503619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4426729958801162168019301 830011867275217906503619)
                    ·
                      rfl

theorem cell23_4849327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 4].length) (baseStart_4849327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849327 prefixEnd_4849327 := by exact prefixLift 4849327
  have htrace : WordTrace (prefixWord ++ tailWord_4849327) baseStart_4849327 baseEnd_4849327 := by
    simpa [prefixWord, tailWord_4849327, baseEnd_4849327] using wordTrace_append hprefix tailTrace_4849327
  have hstable : (prefixWord ++ tailWord_4849327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849327).length < 2 ^ (prefixWord ++ tailWord_4849327).sum := by decide
  have hdescent : baseEnd_4849327 < baseStart_4849327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849330 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_4849330 : Nat := 118140960795 + 4849330 * 2 ^ 59
def prefixEnd_4849330 : Nat := 4983230072969 + 3 ^ 40 * 4849330 * 2
def baseEnd_4849330 : Nat := 2490037142267617207773343

theorem tailTrace_4849330 : CollatzResearch.WordTrace tailWord_4849330 prefixEnd_4849330 2490037142267617207773343 := by
  unfold tailWord_4849330
  simp only [CollatzResearch.WordTrace]
  refine ⟨44217398880428271118192361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117913063681142056315179629 44217398880428271118192361)
  ·
    refine ⟨33163049160321203338644271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44217398880428271118192361 33163049160321203338644271)
    ·
      refine ⟨49744573740481805007966407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33163049160321203338644271 49744573740481805007966407)
      ·
        refine ⟨74616860610722707511949611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49744573740481805007966407 74616860610722707511949611)
        ·
          refine ⟨111925290916084061267924417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74616860610722707511949611 111925290916084061267924417)
          ·
            refine ⟨83943968187063045950943313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111925290916084061267924417 83943968187063045950943313)
            ·
              refine ⟨62957976140297284463207485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83943968187063045950943313 62957976140297284463207485)
              ·
                refine ⟨23609241052611481673702807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62957976140297284463207485 23609241052611481673702807)
                ·
                  refine ⟨35413861578917222510554211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23609241052611481673702807 35413861578917222510554211)
                  ·
                    refine ⟨53120792368375833765831317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35413861578917222510554211 53120792368375833765831317)
                    ·
                      refine ⟨2490037142267617207773343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53120792368375833765831317 2490037142267617207773343)
                      ·
                        rfl

theorem cell23_4849330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_4849330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849330 prefixEnd_4849330 := by exact prefixLift 4849330
  have htrace : WordTrace (prefixWord ++ tailWord_4849330) baseStart_4849330 baseEnd_4849330 := by
    simpa [prefixWord, tailWord_4849330, baseEnd_4849330] using wordTrace_append hprefix tailTrace_4849330
  have hstable : (prefixWord ++ tailWord_4849330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849330).length < 2 ^ (prefixWord ++ tailWord_4849330).sum := by decide
  have hdescent : baseEnd_4849330 < baseStart_4849330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849337 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 3, 2, 3]
def baseStart_4849337 : Nat := 118140960795 + 4849337 * 2 ^ 59
def prefixEnd_4849337 : Nat := 4983230072969 + 3 ^ 40 * 4849337 * 2
def baseEnd_4849337 : Nat := 2490040736632198680385811

theorem tailTrace_4849337 : CollatzResearch.WordTrace tailWord_4849337 prefixEnd_4849337 2490040736632198680385811 := by
  unfold tailWord_4849337
  simp only [CollatzResearch.WordTrace]
  refine ⟨176869850832687724668274265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117913233888458483112182843 176869850832687724668274265)
  ·
    refine ⟨132652388124515793501205699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176869850832687724668274265 132652388124515793501205699)
    ·
      refine ⟨198978582186773690251808549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132652388124515793501205699 198978582186773690251808549)
      ·
        refine ⟨37308484160020066922214103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198978582186773690251808549 37308484160020066922214103)
        ·
          refine ⟨55962726240030100383321155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37308484160020066922214103 55962726240030100383321155)
          ·
            refine ⟨83944089360045150574981733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55962726240030100383321155 83944089360045150574981733)
            ·
              refine ⟨15739516755008465732809075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83944089360045150574981733 15739516755008465732809075)
              ·
                refine ⟨23609275132512698599213613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15739516755008465732809075 23609275132512698599213613)
                ·
                  refine ⟨8853478174692261974705105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23609275132512698599213613 8853478174692261974705105)
                  ·
                    refine ⟨6640108631019196481028829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8853478174692261974705105 6640108631019196481028829)
                    ·
                      refine ⟨2490040736632198680385811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6640108631019196481028829 2490040736632198680385811)
                      ·
                        rfl

theorem cell23_4849337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_4849337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849337 prefixEnd_4849337 := by exact prefixLift 4849337
  have htrace : WordTrace (prefixWord ++ tailWord_4849337) baseStart_4849337 baseEnd_4849337 := by
    simpa [prefixWord, tailWord_4849337, baseEnd_4849337] using wordTrace_append hprefix tailTrace_4849337
  have hstable : (prefixWord ++ tailWord_4849337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849337).length < 2 ^ (prefixWord ++ tailWord_4849337).sum := by decide
  have hdescent : baseEnd_4849337 < baseStart_4849337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849384 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_4849384 : Nat := 118140960795 + 4849384 * 2 ^ 59
def prefixEnd_4849384 : Nat := 4983230072969 + 3 ^ 40 * 4849384 * 2
def baseEnd_4849384 : Nat := 2490064870222959996498095

theorem tailTrace_4849384 : CollatzResearch.WordTrace tailWord_4849384 prefixEnd_4849384 2490064870222959996498095 := by
  unfold tailWord_4849384
  simp only [CollatzResearch.WordTrace]
  refine ⟨88435782531758725847617603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117914376709011634463490137 88435782531758725847617603)
  ·
    refine ⟨132653673797638088771426405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88435782531758725847617603 132653673797638088771426405)
    ·
      refine ⟨24872563837057141644642451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132653673797638088771426405 24872563837057141644642451)
      ·
        refine ⟨37308845755585712466963677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24872563837057141644642451 37308845755585712466963677)
        ·
          refine ⟨13990817158344642175111379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37308845755585712466963677 13990817158344642175111379)
          ·
            refine ⟨20986225737516963262667069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13990817158344642175111379 20986225737516963262667069)
            ·
              refine ⟨7869834651568861223500151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20986225737516963262667069 7869834651568861223500151)
              ·
                refine ⟨11804751977353291835250227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7869834651568861223500151 11804751977353291835250227)
                ·
                  refine ⟨17707127966029937752875341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11804751977353291835250227 17707127966029937752875341)
                  ·
                    refine ⟨6640172987261226657328253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17707127966029937752875341 6640172987261226657328253)
                    ·
                      refine ⟨2490064870222959996498095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6640172987261226657328253 2490064870222959996498095)
                      ·
                        rfl

theorem cell23_4849384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_4849384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849384 prefixEnd_4849384 := by exact prefixLift 4849384
  have htrace : WordTrace (prefixWord ++ tailWord_4849384) baseStart_4849384 baseEnd_4849384 := by
    simpa [prefixWord, tailWord_4849384, baseEnd_4849384] using wordTrace_append hprefix tailTrace_4849384
  have hstable : (prefixWord ++ tailWord_4849384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849384).length < 2 ^ (prefixWord ++ tailWord_4849384).sum := by decide
  have hdescent : baseEnd_4849384 < baseStart_4849384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849400 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 4, 6]
def baseStart_4849400 : Nat := 118140960795 + 4849400 * 2 ^ 59
def prefixEnd_4849400 : Nat := 4983230072969 + 3 ^ 40 * 4849400 * 2
def baseEnd_4849400 : Nat := 830024361971143977966007

theorem tailTrace_4849400 : CollatzResearch.WordTrace tailWord_4849400 prefixEnd_4849400 830024361971143977966007 := by
  unfold tailWord_4849400
  simp only [CollatzResearch.WordTrace]
  refine ⟨88436074315729743213908827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117914765754306324285211769 88436074315729743213908827)
  ·
    refine ⟨132654111473594614820863241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88436074315729743213908827 132654111473594614820863241)
    ·
      refine ⟨99490583605195961115647431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132654111473594614820863241 99490583605195961115647431)
      ·
        refine ⟨149235875407793941673471147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99490583605195961115647431 149235875407793941673471147)
        ·
          refine ⟨223853813111690912510206721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149235875407793941673471147 223853813111690912510206721)
          ·
            refine ⟨167890359833768184382655041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223853813111690912510206721 167890359833768184382655041)
            ·
              refine ⟨125917769875326138286991281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167890359833768184382655041 125917769875326138286991281)
              ·
                refine ⟨94438327406494603715243461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125917769875326138286991281 94438327406494603715243461)
                ·
                  refine ⟨17707186388717738196608149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94438327406494603715243461 17707186388717738196608149)
                  ·
                    refine ⟨830024361971143977966007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17707186388717738196608149 830024361971143977966007)
                    ·
                      rfl

theorem cell23_4849400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_4849400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849400 prefixEnd_4849400 := by exact prefixLift 4849400
  have htrace : WordTrace (prefixWord ++ tailWord_4849400) baseStart_4849400 baseEnd_4849400 := by
    simpa [prefixWord, tailWord_4849400, baseEnd_4849400] using wordTrace_append hprefix tailTrace_4849400
  have hstable : (prefixWord ++ tailWord_4849400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849400).length < 2 ^ (prefixWord ++ tailWord_4849400).sum := by decide
  have hdescent : baseEnd_4849400 < baseStart_4849400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849477 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 2, 5]
def baseStart_4849477 : Nat := 118140960795 + 4849477 * 2 ^ 59
def prefixEnd_4849477 : Nat := 4983230072969 + 3 ^ 40 * 4849477 * 2
def baseEnd_4849477 : Nat := 830037541307942710878389

theorem tailTrace_4849477 : CollatzResearch.WordTrace tailWord_4849477 prefixEnd_4849477 830037541307942710878389 := by
  unfold tailWord_4849477
  simp only [CollatzResearch.WordTrace]
  refine ⟨176874957052180528578370685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117916638034787019052247123 176874957052180528578370685)
  ·
    refine ⟨66328108894567698216889007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176874957052180528578370685 66328108894567698216889007)
    ·
      refine ⟨99492163341851547325333511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66328108894567698216889007 99492163341851547325333511)
      ·
        refine ⟨149238245012777320988000267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99492163341851547325333511 149238245012777320988000267)
        ·
          refine ⟨223857367519165981482000401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149238245012777320988000267 223857367519165981482000401)
          ·
            refine ⟨167893025639374486111500301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223857367519165981482000401 167893025639374486111500301)
            ·
              refine ⟨62959884614765432291812613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167893025639374486111500301 62959884614765432291812613)
              ·
                refine ⟨11804978365268518554714865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62959884614765432291812613 11804978365268518554714865)
                ·
                  refine ⟨8853733773951388916036149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11804978365268518554714865 8853733773951388916036149)
                  ·
                    refine ⟨830037541307942710878389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8853733773951388916036149 830037541307942710878389)
                    ·
                      rfl

theorem cell23_4849477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_4849477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849477 prefixEnd_4849477 := by exact prefixLift 4849477
  have htrace : WordTrace (prefixWord ++ tailWord_4849477) baseStart_4849477 baseEnd_4849477 := by
    simpa [prefixWord, tailWord_4849477, baseEnd_4849477] using wordTrace_append hprefix tailTrace_4849477
  have hstable : (prefixWord ++ tailWord_4849477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849477).length < 2 ^ (prefixWord ++ tailWord_4849477).sum := by decide
  have hdescent : baseEnd_4849477 < baseStart_4849477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849497 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 1, 3, 4]
def baseStart_4849497 : Nat := 118140960795 + 4849497 * 2 ^ 59
def prefixEnd_4849497 : Nat := 4983230072969 + 3 ^ 40 * 4849497 * 2
def baseEnd_4849497 : Nat := 2490122893536918054385075

theorem tailTrace_4849497 : CollatzResearch.WordTrace tailWord_4849497 prefixEnd_4849497 2490122893536918054385075 := by
  unfold tailWord_4849497
  simp only [CollatzResearch.WordTrace]
  refine ⟨176875686512108071994098745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117917124341405381329399163 176875686512108071994098745)
  ·
    refine ⟨132656764884081053995574059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176875686512108071994098745 132656764884081053995574059)
    ·
      refine ⟨198985147326121580993361089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132656764884081053995574059 198985147326121580993361089)
      ·
        refine ⟨149238860494591185745020817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198985147326121580993361089 149238860494591185745020817)
        ·
          refine ⟨111929145370943389308765613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149238860494591185745020817 111929145370943389308765613)
          ·
            refine ⟨41973429514103770990787105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111929145370943389308765613 41973429514103770990787105)
            ·
              refine ⟨31480072135577828243090329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41973429514103770990787105 31480072135577828243090329)
              ·
                refine ⟨23610054101683371182317747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31480072135577828243090329 23610054101683371182317747)
                ·
                  refine ⟨35415081152525056773476621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23610054101683371182317747 35415081152525056773476621)
                  ·
                    refine ⟨13280655432196896290053733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35415081152525056773476621 13280655432196896290053733)
                    ·
                      refine ⟨2490122893536918054385075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13280655432196896290053733 2490122893536918054385075)
                      ·
                        rfl

theorem cell23_4849497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_4849497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849497 prefixEnd_4849497 := by exact prefixLift 4849497
  have htrace : WordTrace (prefixWord ++ tailWord_4849497) baseStart_4849497 baseEnd_4849497 := by
    simpa [prefixWord, tailWord_4849497, baseEnd_4849497] using wordTrace_append hprefix tailTrace_4849497
  have hstable : (prefixWord ++ tailWord_4849497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849497).length < 2 ^ (prefixWord ++ tailWord_4849497).sum := by decide
  have hdescent : baseEnd_4849497 < baseStart_4849497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849541 : List Nat := [1, 3, 1, 1, 3, 2, 1, 6, 1, 4]
def baseStart_4849541 : Nat := 118140960795 + 4849541 * 2 ^ 59
def prefixEnd_4849541 : Nat := 4983230072969 + 3 ^ 40 * 4849541 * 2
def baseEnd_4849541 : Nat := 830048495561905294078291

theorem tailTrace_4849541 : CollatzResearch.WordTrace tailWord_4849541 prefixEnd_4849541 830048495561905294078291 := by
  unfold tailWord_4849541
  simp only [CollatzResearch.WordTrace]
  refine ⟨176877291323948667508700477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117918194215965778339133651 176877291323948667508700477)
  ·
    refine ⟨66328984246480750315762679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176877291323948667508700477 66328984246480750315762679)
    ·
      refine ⟨99493476369721125473644019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66328984246480750315762679 99493476369721125473644019)
      ·
        refine ⟨149240214554581688210466029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99493476369721125473644019 149240214554581688210466029)
        ·
          refine ⟨55965080457968133078924761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149240214554581688210466029 55965080457968133078924761)
          ·
            refine ⟨41973810343476099809193571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55965080457968133078924761 41973810343476099809193571)
            ·
              refine ⟨62960715515214149713790357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41973810343476099809193571 62960715515214149713790357)
              ·
                refine ⟨2951283539775663267833923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62960715515214149713790357 2951283539775663267833923)
                ·
                  refine ⟨4426925309663494901750885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2951283539775663267833923 4426925309663494901750885)
                  ·
                    refine ⟨830048495561905294078291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4426925309663494901750885 830048495561905294078291)
                    ·
                      rfl

theorem cell23_4849541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_4849541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849541 prefixEnd_4849541 := by exact prefixLift 4849541
  have htrace : WordTrace (prefixWord ++ tailWord_4849541) baseStart_4849541 baseEnd_4849541 := by
    simpa [prefixWord, tailWord_4849541, baseEnd_4849541] using wordTrace_append hprefix tailTrace_4849541
  have hstable : (prefixWord ++ tailWord_4849541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849541).length < 2 ^ (prefixWord ++ tailWord_4849541).sum := by decide
  have hdescent : baseEnd_4849541 < baseStart_4849541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849557 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_4849557 : Nat := 118140960795 + 4849557 * 2 ^ 59
def prefixEnd_4849557 : Nat := 4983230072969 + 3 ^ 40 * 4849557 * 2
def baseEnd_4849557 : Nat := 2490153702376187819634799

theorem tailTrace_4849557 : CollatzResearch.WordTrace tailWord_4849557 prefixEnd_4849557 2490153702376187819634799 := by
  unfold tailWord_4849557
  simp only [CollatzResearch.WordTrace]
  refine ⟨176877874891890702241282925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117918583261260468160855283 176877874891890702241282925)
  ·
    refine ⟨66329203084459013340481097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176877874891890702241282925 66329203084459013340481097)
    ·
      refine ⟨49746902313344260005360823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66329203084459013340481097 49746902313344260005360823)
      ·
        refine ⟨74620353470016390008041235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49746902313344260005360823 74620353470016390008041235)
        ·
          refine ⟨111930530205024585012061853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74620353470016390008041235 111930530205024585012061853)
          ·
            refine ⟨41973948826884219379523195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111930530205024585012061853 41973948826884219379523195)
            ·
              refine ⟨62960923240326329069284793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41973948826884219379523195 62960923240326329069284793)
              ·
                refine ⟨47220692430244746801963595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62960923240326329069284793 47220692430244746801963595)
                ·
                  refine ⟨70831038645367120202945393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47220692430244746801963595 70831038645367120202945393)
                  ·
                    refine ⟨53123278984025340152209045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70831038645367120202945393 53123278984025340152209045)
                    ·
                      refine ⟨2490153702376187819634799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53123278984025340152209045 2490153702376187819634799)
                      ·
                        rfl

theorem cell23_4849557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_4849557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849557 prefixEnd_4849557 := by exact prefixLift 4849557
  have htrace : WordTrace (prefixWord ++ tailWord_4849557) baseStart_4849557 baseEnd_4849557 := by
    simpa [prefixWord, tailWord_4849557, baseEnd_4849557] using wordTrace_append hprefix tailTrace_4849557
  have hstable : (prefixWord ++ tailWord_4849557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849557).length < 2 ^ (prefixWord ++ tailWord_4849557).sum := by decide
  have hdescent : baseEnd_4849557 < baseStart_4849557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849575 : List Nat := [1, 1, 6, 1, 2, 3, 1, 3, 1, 4]
def baseStart_4849575 : Nat := 118140960795 + 4849575 * 2 ^ 59
def prefixEnd_4849575 : Nat := 4983230072969 + 3 ^ 40 * 4849575 * 2
def baseEnd_4849575 : Nat := 830054315009322916403239

theorem tailTrace_4849575 : CollatzResearch.WordTrace tailWord_4849575 prefixEnd_4849575 830054315009322916403239 := by
  unfold tailWord_4849575
  simp only [CollatzResearch.WordTrace]
  refine ⟨176878531405825491315438179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117919020937216994210292119 176878531405825491315438179)
  ·
    refine ⟨265317797108738236973157269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176878531405825491315438179 265317797108738236973157269)
    ·
      refine ⟨12436771739472104858116747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 265317797108738236973157269 12436771739472104858116747)
      ·
        refine ⟨18655157609208157287175121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12436771739472104858116747 18655157609208157287175121)
        ·
          refine ⟨13991368206906117965381341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18655157609208157287175121 13991368206906117965381341)
          ·
            refine ⟨5246763077589794237018003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13991368206906117965381341 5246763077589794237018003)
            ·
              refine ⟨7870144616384691355527005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5246763077589794237018003 7870144616384691355527005)
              ·
                refine ⟨2951304231144259258322627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7870144616384691355527005 2951304231144259258322627)
                ·
                  refine ⟨4426956346716388887483941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2951304231144259258322627 4426956346716388887483941)
                  ·
                    refine ⟨830054315009322916403239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4426956346716388887483941 830054315009322916403239)
                    ·
                      rfl

theorem cell23_4849575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_4849575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849575 prefixEnd_4849575 := by exact prefixLift 4849575
  have htrace : WordTrace (prefixWord ++ tailWord_4849575) baseStart_4849575 baseEnd_4849575 := by
    simpa [prefixWord, tailWord_4849575, baseEnd_4849575] using wordTrace_append hprefix tailTrace_4849575
  have hstable : (prefixWord ++ tailWord_4849575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849575).length < 2 ^ (prefixWord ++ tailWord_4849575).sum := by decide
  have hdescent : baseEnd_4849575 < baseStart_4849575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849598 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_4849598 : Nat := 118140960795 + 4849598 * 2 ^ 59
def prefixEnd_4849598 : Nat := 4983230072969 + 3 ^ 40 * 4849598 * 2
def baseEnd_4849598 : Nat := 2490174755083022159222111

theorem tailTrace_4849598 : CollatzResearch.WordTrace tailWord_4849598 prefixEnd_4849598 2490174755083022159222111 := by
  unfold tailWord_4849598
  simp only [CollatzResearch.WordTrace]
  refine ⟨22109921285592770780440681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117919580189828110829016965 22109921285592770780440681)
  ·
    refine ⟨16582440964194578085330511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22109921285592770780440681 16582440964194578085330511)
    ·
      refine ⟨24873661446291867127995767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16582440964194578085330511 24873661446291867127995767)
      ·
        refine ⟨37310492169437800691993651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24873661446291867127995767 37310492169437800691993651)
        ·
          refine ⟨55965738254156701037990477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37310492169437800691993651 55965738254156701037990477)
          ·
            refine ⟨20987151845308762889246429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55965738254156701037990477 20987151845308762889246429)
            ·
              refine ⟨7870181941990786083467411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20987151845308762889246429 7870181941990786083467411)
              ·
                refine ⟨11805272912986179125201117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7870181941990786083467411 11805272912986179125201117)
                ·
                  refine ⟨4426977342369817171950419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11805272912986179125201117 4426977342369817171950419)
                  ·
                    refine ⟨6640466013554725757925629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4426977342369817171950419 6640466013554725757925629)
                    ·
                      refine ⟨2490174755083022159222111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6640466013554725757925629 2490174755083022159222111)
                      ·
                        rfl

theorem cell23_4849598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_4849598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849598 prefixEnd_4849598 := by exact prefixLift 4849598
  have htrace : WordTrace (prefixWord ++ tailWord_4849598) baseStart_4849598 baseEnd_4849598 := by
    simpa [prefixWord, tailWord_4849598, baseEnd_4849598] using wordTrace_append hprefix tailTrace_4849598
  have hstable : (prefixWord ++ tailWord_4849598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849598).length < 2 ^ (prefixWord ++ tailWord_4849598).sum := by decide
  have hdescent : baseEnd_4849598 < baseStart_4849598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849614 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_4849614 : Nat := 118140960795 + 4849614 * 2 ^ 59
def prefixEnd_4849614 : Nat := 4983230072969 + 3 ^ 40 * 4849614 * 2
def baseEnd_4849614 : Nat := 830060990257831365540679

theorem tailTrace_4849614 : CollatzResearch.WordTrace tailWord_4849614 prefixEnd_4849614 830060990257831365540679 := by
  unfold tailWord_4849614
  simp only [CollatzResearch.WordTrace]
  refine ⟨22109994231585525122013487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117919969235122800650738597 22109994231585525122013487)
  ·
    refine ⟨33164991347378287683020231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22109994231585525122013487 33164991347378287683020231)
    ·
      refine ⟨49747487021067431524530347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33164991347378287683020231 49747487021067431524530347)
      ·
        refine ⟨74621230531601147286795521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49747487021067431524530347 74621230531601147286795521)
        ·
          refine ⟨55965922898700860465096641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74621230531601147286795521 55965922898700860465096641)
          ·
            refine ⟨41974442174025645348822481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55965922898700860465096641 41974442174025645348822481)
            ·
              refine ⟨31480831630519234011616861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41974442174025645348822481 31480831630519234011616861)
              ·
                refine ⟨11805311861444712754356323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31480831630519234011616861 11805311861444712754356323)
                ·
                  refine ⟨17707967792167069131534485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11805311861444712754356323 17707967792167069131534485)
                  ·
                    refine ⟨830060990257831365540679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17707967792167069131534485 830060990257831365540679)
                    ·
                      rfl

theorem cell23_4849614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_4849614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849614 prefixEnd_4849614 := by exact prefixLift 4849614
  have htrace : WordTrace (prefixWord ++ tailWord_4849614) baseStart_4849614 baseEnd_4849614 := by
    simpa [prefixWord, tailWord_4849614, baseEnd_4849614] using wordTrace_append hprefix tailTrace_4849614
  have hstable : (prefixWord ++ tailWord_4849614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849614).length < 2 ^ (prefixWord ++ tailWord_4849614).sum := by decide
  have hdescent : baseEnd_4849614 < baseStart_4849614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849621 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_4849621 : Nat := 118140960795 + 4849621 * 2 ^ 59
def prefixEnd_4849621 : Nat := 4983230072969 + 3 ^ 40 * 4849621 * 2
def baseEnd_4849621 : Nat := 2490186565138075569234505

theorem tailTrace_4849621 : CollatzResearch.WordTrace tailWord_4849621 prefixEnd_4849621 2490186565138075569234505 := by
  unfold tailWord_4849621
  simp only [CollatzResearch.WordTrace]
  refine ⟨176880209163658841171612717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117920139442439227447741811 176880209163658841171612717)
  ·
    refine ⟨66330078436372065439354769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176880209163658841171612717 66330078436372065439354769)
    ·
      refine ⟨49747558827279049079516077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66330078436372065439354769 49747558827279049079516077)
      ·
        refine ⟨18655334560229643404818529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49747558827279049079516077 18655334560229643404818529)
        ·
          refine ⟨13991500920172232553613897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18655334560229643404818529 13991500920172232553613897)
          ·
            refine ⟨10493625690129174415210423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13991500920172232553613897 10493625690129174415210423)
            ·
              refine ⟨15740438535193761622815635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10493625690129174415210423 15740438535193761622815635)
              ·
                refine ⟨23610657802790642434223453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15740438535193761622815635 23610657802790642434223453)
                ·
                  refine ⟨8853996676046490912833795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23610657802790642434223453 8853996676046490912833795)
                  ·
                    refine ⟨13280995014069736369250693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8853996676046490912833795 13280995014069736369250693)
                    ·
                      refine ⟨2490186565138075569234505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13280995014069736369250693 2490186565138075569234505)
                      ·
                        rfl

theorem cell23_4849621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_4849621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849621 prefixEnd_4849621 := by exact prefixLift 4849621
  have htrace : WordTrace (prefixWord ++ tailWord_4849621) baseStart_4849621 baseEnd_4849621 := by
    simpa [prefixWord, tailWord_4849621, baseEnd_4849621] using wordTrace_append hprefix tailTrace_4849621
  have hstable : (prefixWord ++ tailWord_4849621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849621).length < 2 ^ (prefixWord ++ tailWord_4849621).sum := by decide
  have hdescent : baseEnd_4849621 < baseStart_4849621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849649 : List Nat := [1, 2, 2, 2, 6, 1, 2, 2, 1, 1, 3]
def baseStart_4849649 : Nat := 118140960795 + 4849649 * 2 ^ 59
def prefixEnd_4849649 : Nat := 4983230072969 + 3 ^ 40 * 4849649 * 2
def baseEnd_4849649 : Nat := 2490200942596401459684377

theorem tailTrace_4849649 : CollatzResearch.WordTrace tailWord_4849649 prefixEnd_4849649 2490200942596401459684377 := by
  unfold tailWord_4849649
  simp only [CollatzResearch.WordTrace]
  refine ⟨176881230407557401953632001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117920820271704934635754667 176881230407557401953632001)
  ·
    refine ⟨132660922805668051465224001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176881230407557401953632001 132660922805668051465224001)
    ·
      refine ⟨99495692104251038598918001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132660922805668051465224001 99495692104251038598918001)
      ·
        refine ⟨74621769078188278949188501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99495692104251038598918001 74621769078188278949188501)
        ·
          refine ⟨3497895425540075575743211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74621769078188278949188501 3497895425540075575743211)
          ·
            refine ⟨5246843138310113363614817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3497895425540075575743211 5246843138310113363614817)
            ·
              refine ⟨3935132353732585022711113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5246843138310113363614817 3935132353732585022711113)
              ·
                refine ⟨2951349265299438767033335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3935132353732585022711113 2951349265299438767033335)
                ·
                  refine ⟨4427023897949158150550003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2951349265299438767033335 4427023897949158150550003)
                  ·
                    refine ⟨6640535846923737225825005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4427023897949158150550003 6640535846923737225825005)
                    ·
                      refine ⟨2490200942596401459684377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6640535846923737225825005 2490200942596401459684377)
                      ·
                        rfl

theorem cell23_4849649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_4849649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849649 prefixEnd_4849649 := by exact prefixLift 4849649
  have htrace : WordTrace (prefixWord ++ tailWord_4849649) baseStart_4849649 baseEnd_4849649 := by
    simpa [prefixWord, tailWord_4849649, baseEnd_4849649] using wordTrace_append hprefix tailTrace_4849649
  have hstable : (prefixWord ++ tailWord_4849649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849649).length < 2 ^ (prefixWord ++ tailWord_4849649).sum := by decide
  have hdescent : baseEnd_4849649 < baseStart_4849649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849671 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_4849671 : Nat := 118140960795 + 4849671 * 2 ^ 59
def prefixEnd_4849671 : Nat := 4983230072969 + 3 ^ 40 * 4849671 * 2
def baseEnd_4849671 : Nat := 2490212239170800373609275

theorem tailTrace_4849671 : CollatzResearch.WordTrace tailWord_4849671 prefixEnd_4849671 2490212239170800373609275 := by
  unfold tailWord_4849671
  simp only [CollatzResearch.WordTrace]
  refine ⟨176882032813477699710932867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117921355208985133140621911 176882032813477699710932867)
  ·
    refine ⟨265323049220216549566399301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176882032813477699710932867 265323049220216549566399301)
    ·
      refine ⟨49748071728790603043699869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265323049220216549566399301 49748071728790603043699869)
      ·
        refine ⟨18655526898296476141387451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49748071728790603043699869 18655526898296476141387451)
        ·
          refine ⟨27983290347444714212081177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18655526898296476141387451 27983290347444714212081177)
          ·
            refine ⟨20987467760583535659060883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27983290347444714212081177 20987467760583535659060883)
            ·
              refine ⟨31481201640875303488591325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20987467760583535659060883 31481201640875303488591325)
              ·
                refine ⟨11805450615328238808221747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31481201640875303488591325 11805450615328238808221747)
                ·
                  refine ⟨17708175922992358212332621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11805450615328238808221747 17708175922992358212332621)
                  ·
                    refine ⟨6640565971122134329624733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17708175922992358212332621 6640565971122134329624733)
                    ·
                      refine ⟨2490212239170800373609275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6640565971122134329624733 2490212239170800373609275)
                      ·
                        rfl

theorem cell23_4849671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_4849671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849671 prefixEnd_4849671 := by exact prefixLift 4849671
  have htrace : WordTrace (prefixWord ++ tailWord_4849671) baseStart_4849671 baseEnd_4849671 := by
    simpa [prefixWord, tailWord_4849671, baseEnd_4849671] using wordTrace_append hprefix tailTrace_4849671
  have hstable : (prefixWord ++ tailWord_4849671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849671).length < 2 ^ (prefixWord ++ tailWord_4849671).sum := by decide
  have hdescent : baseEnd_4849671 < baseStart_4849671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849728 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 1, 4, 2]
def baseStart_4849728 : Nat := 118140960795 + 4849728 * 2 ^ 59
def prefixEnd_4849728 : Nat := 4983230072969 + 3 ^ 40 * 4849728 * 2
def baseEnd_4849728 : Nat := 2490241507568106650596513

theorem tailTrace_4849728 : CollatzResearch.WordTrace tailWord_4849728 prefixEnd_4849728 2490241507568106650596513 := by
  unfold tailWord_4849728
  simp only [CollatzResearch.WordTrace]
  refine ⟨88442055887135599222878919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117922741182847465630505225 88442055887135599222878919)
  ·
    refine ⟨132663083830703398834318379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88442055887135599222878919 132663083830703398834318379)
    ·
      refine ⟨198994625746055098251477569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132663083830703398834318379 198994625746055098251477569)
      ·
        refine ⟨149245969309541323688608177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198994625746055098251477569 149245969309541323688608177)
        ·
          refine ⟨111934476982155992766456133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149245969309541323688608177 111934476982155992766456133)
          ·
            refine ⟨20987714434154248643710525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111934476982155992766456133 20987714434154248643710525)
            ·
              refine ⟨7870392912807843241391447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20987714434154248643710525 7870392912807843241391447)
              ·
                refine ⟨11805589369211764862087171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7870392912807843241391447 11805589369211764862087171)
                ·
                  refine ⟨17708384053817647293130757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11805589369211764862087171 17708384053817647293130757)
                  ·
                    refine ⟨3320322010090808867462017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17708384053817647293130757 3320322010090808867462017)
                    ·
                      refine ⟨2490241507568106650596513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3320322010090808867462017 2490241507568106650596513)
                      ·
                        rfl

theorem cell23_4849728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 4, 2].length) (baseStart_4849728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849728 prefixEnd_4849728 := by exact prefixLift 4849728
  have htrace : WordTrace (prefixWord ++ tailWord_4849728) baseStart_4849728 baseEnd_4849728 := by
    simpa [prefixWord, tailWord_4849728, baseEnd_4849728] using wordTrace_append hprefix tailTrace_4849728
  have hstable : (prefixWord ++ tailWord_4849728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849728).length < 2 ^ (prefixWord ++ tailWord_4849728).sum := by decide
  have hdescent : baseEnd_4849728 < baseStart_4849728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849804 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_4849804 : Nat := 118140960795 + 4849804 * 2 ^ 59
def prefixEnd_4849804 : Nat := 4983230072969 + 3 ^ 40 * 4849804 * 2
def baseEnd_4849804 : Nat := 2490280532097848353246163

theorem tailTrace_4849804 : CollatzResearch.WordTrace tailWord_4849804 prefixEnd_4849804 2490280532097848353246163 := by
  unfold tailWord_4849804
  simp only [CollatzResearch.WordTrace]
  refine ⟨88443441860997931712762233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117924589147997242283682977 88443441860997931712762233)
  ·
    refine ⟨66332581395748448784571675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88443441860997931712762233 66332581395748448784571675)
    ·
      refine ⟨99498872093622673176857513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66332581395748448784571675 99498872093622673176857513)
      ·
        refine ⟨74624154070217004882643135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99498872093622673176857513 74624154070217004882643135)
        ·
          refine ⟨111936231105325507323964703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74624154070217004882643135 111936231105325507323964703)
          ·
            refine ⟨167904346657988260985947055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111936231105325507323964703 167904346657988260985947055)
            ·
              refine ⟨251856519986982391478920583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167904346657988260985947055 251856519986982391478920583)
              ·
                refine ⟨377784779980473587218380875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251856519986982391478920583 377784779980473587218380875)
                ·
                  refine ⟨566677169970710380827571313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 377784779980473587218380875 566677169970710380827571313)
                  ·
                    refine ⟨425007877478032785620678485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 566677169970710380827571313 425007877478032785620678485)
                    ·
                      refine ⟨2490280532097848353246163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 425007877478032785620678485 2490280532097848353246163)
                      ·
                        rfl

theorem cell23_4849804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_4849804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849804 prefixEnd_4849804 := by exact prefixLift 4849804
  have htrace : WordTrace (prefixWord ++ tailWord_4849804) baseStart_4849804 baseEnd_4849804 := by
    simpa [prefixWord, tailWord_4849804, baseEnd_4849804] using wordTrace_append hprefix tailTrace_4849804
  have hstable : (prefixWord ++ tailWord_4849804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849804).length < 2 ^ (prefixWord ++ tailWord_4849804).sum := by decide
  have hdescent : baseEnd_4849804 < baseStart_4849804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849852 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 2, 1, 4]
def baseStart_4849852 : Nat := 118140960795 + 4849852 * 2 ^ 59
def prefixEnd_4849852 : Nat := 4983230072969 + 3 ^ 40 * 4849852 * 2
def baseEnd_4849852 : Nat := 2490305179169264165445943

theorem tailTrace_4849852 : CollatzResearch.WordTrace tailWord_4849852 prefixEnd_4849852 2490305179169264165445943 := by
  unfold tailWord_4849852
  simp only [CollatzResearch.WordTrace]
  refine ⟨88444317212910983811635905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117925756283881311748847873 88444317212910983811635905)
  ·
    refine ⟨66333237909683237858726929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88444317212910983811635905 66333237909683237858726929)
    ·
      refine ⟨49749928432262428394045197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66333237909683237858726929 49749928432262428394045197)
      ·
        refine ⟨18656223162098410647766949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49749928432262428394045197 18656223162098410647766949)
        ·
          refine ⟨3498041842893451996456303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18656223162098410647766949 3498041842893451996456303)
          ·
            refine ⟨5247062764340177994684455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3498041842893451996456303 5247062764340177994684455)
            ·
              refine ⟨7870594146510266992026683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5247062764340177994684455 7870594146510266992026683)
              ·
                refine ⟨11805891219765400488040025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7870594146510266992026683 11805891219765400488040025)
                ·
                  refine ⟨8854418414824050366030019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11805891219765400488040025 8854418414824050366030019)
                  ·
                    refine ⟨13281627622236075549045029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8854418414824050366030019 13281627622236075549045029)
                    ·
                      refine ⟨2490305179169264165445943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13281627622236075549045029 2490305179169264165445943)
                      ·
                        rfl

theorem cell23_4849852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_4849852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849852 prefixEnd_4849852 := by exact prefixLift 4849852
  have htrace : WordTrace (prefixWord ++ tailWord_4849852) baseStart_4849852 baseEnd_4849852 := by
    simpa [prefixWord, tailWord_4849852, baseEnd_4849852] using wordTrace_append hprefix tailTrace_4849852
  have hstable : (prefixWord ++ tailWord_4849852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849852).length < 2 ^ (prefixWord ++ tailWord_4849852).sum := by decide
  have hdescent : baseEnd_4849852 < baseStart_4849852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849895 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_4849895 : Nat := 118140960795 + 4849895 * 2 ^ 59
def prefixEnd_4849895 : Nat := 4983230072969 + 3 ^ 40 * 4849895 * 2
def baseEnd_4849895 : Nat := 2490327258837407497208245

theorem tailTrace_4849895 : CollatzResearch.WordTrace tailWord_4849895 prefixEnd_4849895 2490327258837407497208245 := by
  unfold tailWord_4849895
  simp only [CollatzResearch.WordTrace]
  refine ⟨176890202764666185967087139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117926801843110790644724759 176890202764666185967087139)
  ·
    refine ⟨265335304146999278950630709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176890202764666185967087139 265335304146999278950630709)
    ·
      refine ⟨24875184763781182401621629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 265335304146999278950630709 24875184763781182401621629)
      ·
        refine ⟨9328194286417943400608111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24875184763781182401621629 9328194286417943400608111)
        ·
          refine ⟨13992291429626915100912167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9328194286417943400608111 13992291429626915100912167)
          ·
            refine ⟨20988437144440372651368251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13992291429626915100912167 20988437144440372651368251)
            ·
              refine ⟨31482655716660558977052377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20988437144440372651368251 31482655716660558977052377)
              ·
                refine ⟨23611991787495419232789283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31482655716660558977052377 23611991787495419232789283)
                ·
                  refine ⟨35417987681243128849183925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23611991787495419232789283 35417987681243128849183925)
                  ·
                    refine ⟨3320436345116543329610993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35417987681243128849183925 3320436345116543329610993)
                    ·
                      refine ⟨2490327258837407497208245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3320436345116543329610993 2490327258837407497208245)
                      ·
                        rfl

theorem cell23_4849895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_4849895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849895 prefixEnd_4849895 := by exact prefixLift 4849895
  have htrace : WordTrace (prefixWord ++ tailWord_4849895) baseStart_4849895 baseEnd_4849895 := by
    simpa [prefixWord, tailWord_4849895, baseEnd_4849895] using wordTrace_append hprefix tailTrace_4849895
  have hstable : (prefixWord ++ tailWord_4849895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849895).length < 2 ^ (prefixWord ++ tailWord_4849895).sum := by decide
  have hdescent : baseEnd_4849895 < baseStart_4849895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849918 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_4849918 : Nat := 118140960795 + 4849918 * 2 ^ 59
def prefixEnd_4849918 : Nat := 4983230072969 + 3 ^ 40 * 4849918 * 2
def baseEnd_4849918 : Nat := 830113022964153635740213

theorem tailTrace_4849918 : CollatzResearch.WordTrace tailWord_4849918 prefixEnd_4849918 830113022964153635740213 := by
  unfold tailWord_4849918
  simp only [CollatzResearch.WordTrace]
  refine ⟨22111380205447857611896801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117927361095721907263449605 22111380205447857611896801)
  ·
    refine ⟨16583535154085893208922601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22111380205447857611896801 16583535154085893208922601)
    ·
      refine ⟨12437651365564419906691951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16583535154085893208922601 12437651365564419906691951)
      ·
        refine ⟨18656477048346629860037927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12437651365564419906691951 18656477048346629860037927)
        ·
          refine ⟨27984715572519944790056891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18656477048346629860037927 27984715572519944790056891)
          ·
            refine ⟨41977073358779917185085337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27984715572519944790056891 41977073358779917185085337)
            ·
              refine ⟨31482805019084937888814003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41977073358779917185085337 31482805019084937888814003)
              ·
                refine ⟨47224207528627406833221005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31482805019084937888814003 47224207528627406833221005)
                ·
                  refine ⟨17709077823235277562457877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47224207528627406833221005 17709077823235277562457877)
                  ·
                    refine ⟨830113022964153635740213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17709077823235277562457877 830113022964153635740213)
                    ·
                      rfl

theorem cell23_4849918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_4849918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849918 prefixEnd_4849918 := by exact prefixLift 4849918
  have htrace : WordTrace (prefixWord ++ tailWord_4849918) baseStart_4849918 baseEnd_4849918 := by
    simpa [prefixWord, tailWord_4849918, baseEnd_4849918] using wordTrace_append hprefix tailTrace_4849918
  have hstable : (prefixWord ++ tailWord_4849918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849918).length < 2 ^ (prefixWord ++ tailWord_4849918).sum := by decide
  have hdescent : baseEnd_4849918 < baseStart_4849918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849928 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_4849928 : Nat := 118140960795 + 4849928 * 2 ^ 59
def prefixEnd_4849928 : Nat := 4983230072969 + 3 ^ 40 * 4849928 * 2
def baseEnd_4849928 : Nat := 2490344203699005868095593

theorem tailTrace_4849928 : CollatzResearch.WordTrace tailWord_4849928 prefixEnd_4849928 2490344203699005868095593 := by
  unfold tailWord_4849928
  simp only [CollatzResearch.WordTrace]
  refine ⟨88445703186773316301519219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117927604249031088402025625 88445703186773316301519219)
  ·
    refine ⟨132668554780159974452278829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88445703186773316301519219 132668554780159974452278829)
    ·
      refine ⟨49750708042559990419604561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132668554780159974452278829 49750708042559990419604561)
      ·
        refine ⟨37313031031919992814703421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49750708042559990419604561 37313031031919992814703421)
        ·
          refine ⟨13992386636969997305513783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37313031031919992814703421 13992386636969997305513783)
          ·
            refine ⟨20988579955454995958270675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13992386636969997305513783 20988579955454995958270675)
            ·
              refine ⟨31482869933182493937406013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20988579955454995958270675 31482869933182493937406013)
              ·
                refine ⟨11806076224943435226527255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31482869933182493937406013 11806076224943435226527255)
                ·
                  refine ⟨17709114337415152839790883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11806076224943435226527255 17709114337415152839790883)
                  ·
                    refine ⟨26563671506122729259686325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17709114337415152839790883 26563671506122729259686325)
                    ·
                      refine ⟨2490344203699005868095593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26563671506122729259686325 2490344203699005868095593)
                      ·
                        rfl

theorem cell23_4849928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_4849928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849928 prefixEnd_4849928 := by exact prefixLift 4849928
  have htrace : WordTrace (prefixWord ++ tailWord_4849928) baseStart_4849928 baseEnd_4849928 := by
    simpa [prefixWord, tailWord_4849928, baseEnd_4849928] using wordTrace_append hprefix tailTrace_4849928
  have hstable : (prefixWord ++ tailWord_4849928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849928).length < 2 ^ (prefixWord ++ tailWord_4849928).sum := by decide
  have hdescent : baseEnd_4849928 < baseStart_4849928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849952 : List Nat := [2, 1, 1, 5, 2, 1, 4, 1, 2, 4]
def baseStart_4849952 : Nat := 118140960795 + 4849952 * 2 ^ 59
def prefixEnd_4849952 : Nat := 4983230072969 + 3 ^ 40 * 4849952 * 2
def baseEnd_4849952 : Nat := 830118842411571258065161

theorem tailTrace_4849952 : CollatzResearch.WordTrace tailWord_4849952 prefixEnd_4849952 830118842411571258065161 := by
  unfold tailWord_4849952
  simp only [CollatzResearch.WordTrace]
  refine ⟨88446140862729842350956055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117928187816973123134608073 88446140862729842350956055)
  ·
    refine ⟨132669211294094763526434083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88446140862729842350956055 132669211294094763526434083)
    ·
      refine ⟨199003816941142145289651125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132669211294094763526434083 199003816941142145289651125)
      ·
        refine ⟨18656607838232076120904793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 199003816941142145289651125 18656607838232076120904793)
        ·
          refine ⟨13992455878674057090678595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18656607838232076120904793 13992455878674057090678595)
          ·
            refine ⟨20988683818011085636017893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13992455878674057090678595 20988683818011085636017893)
            ·
              refine ⟨3935378215877078556753355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20988683818011085636017893 3935378215877078556753355)
              ·
                refine ⟨5903067323815617835130033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935378215877078556753355 5903067323815617835130033)
                ·
                  refine ⟨4427300492861713376347525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5903067323815617835130033 4427300492861713376347525)
                  ·
                    refine ⟨830118842411571258065161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4427300492861713376347525 830118842411571258065161)
                    ·
                      rfl

theorem cell23_4849952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 2, 4].length) (baseStart_4849952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849952 prefixEnd_4849952 := by exact prefixLift 4849952
  have htrace : WordTrace (prefixWord ++ tailWord_4849952) baseStart_4849952 baseEnd_4849952 := by
    simpa [prefixWord, tailWord_4849952, baseEnd_4849952] using wordTrace_append hprefix tailTrace_4849952
  have hstable : (prefixWord ++ tailWord_4849952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849952).length < 2 ^ (prefixWord ++ tailWord_4849952).sum := by decide
  have hdescent : baseEnd_4849952 < baseStart_4849952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849959 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4849959 : Nat := 118140960795 + 4849959 * 2 ^ 59
def prefixEnd_4849959 : Nat := 4983230072969 + 3 ^ 40 * 4849959 * 2
def baseEnd_4849959 : Nat := 2490360121599295246807951

theorem tailTrace_4849959 : CollatzResearch.WordTrace tailWord_4849959 prefixEnd_4849959 2490360121599295246807951 := by
  unfold tailWord_4849959
  simp only [CollatzResearch.WordTrace]
  refine ⟨176892537036434324897416931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117928358024289549931611287 176892537036434324897416931)
  ·
    refine ⟨265338805554651487346125397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176892537036434324897416931 265338805554651487346125397)
    ·
      refine ⟨3109439127593572117337407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 265338805554651487346125397 3109439127593572117337407)
      ·
        refine ⟨4664158691390358176006111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3109439127593572117337407 4664158691390358176006111)
        ·
          refine ⟨6996238037085537264009167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664158691390358176006111 6996238037085537264009167)
          ·
            refine ⟨10494357055628305896013751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6996238037085537264009167 10494357055628305896013751)
            ·
              refine ⟨15741535583442458844020627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10494357055628305896013751 15741535583442458844020627)
              ·
                refine ⟨23612303375163688266030941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15741535583442458844020627 23612303375163688266030941)
                ·
                  refine ⟨8854613765686383099761603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23612303375163688266030941 8854613765686383099761603)
                  ·
                    refine ⟨13281920648529574649642405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8854613765686383099761603 13281920648529574649642405)
                    ·
                      refine ⟨2490360121599295246807951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13281920648529574649642405 2490360121599295246807951)
                      ·
                        rfl

theorem cell23_4849959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4849959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849959 prefixEnd_4849959 := by exact prefixLift 4849959
  have htrace : WordTrace (prefixWord ++ tailWord_4849959) baseStart_4849959 baseEnd_4849959 := by
    simpa [prefixWord, tailWord_4849959, baseEnd_4849959] using wordTrace_append hprefix tailTrace_4849959
  have hstable : (prefixWord ++ tailWord_4849959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849959).length < 2 ^ (prefixWord ++ tailWord_4849959).sum := by decide
  have hdescent : baseEnd_4849959 < baseStart_4849959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4849962 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4849962 : Nat := 118140960795 + 4849962 * 2 ^ 59
def prefixEnd_4849962 : Nat := 4983230072969 + 3 ^ 40 * 4849962 * 2
def baseEnd_4849962 : Nat := 2490361662041258735070437

theorem tailTrace_4849962 : CollatzResearch.WordTrace tailWord_4849962 prefixEnd_4849962 2490361662041258735070437 := by
  unfold tailWord_4849962
  simp only [CollatzResearch.WordTrace]
  refine ⟨44223161613855864102444035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117928430970282304273184093 44223161613855864102444035)
  ·
    refine ⟨66334742420783796153666053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44223161613855864102444035 66334742420783796153666053)
    ·
      refine ⟨12437764203896961778812385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66334742420783796153666053 12437764203896961778812385)
      ·
        refine ⟨9328323152922721334109289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12437764203896961778812385 9328323152922721334109289)
        ·
          refine ⟨6996242364692041000581967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9328323152922721334109289 6996242364692041000581967)
          ·
            refine ⟨10494363547038061500872951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6996242364692041000581967 10494363547038061500872951)
            ·
              refine ⟨15741545320557092251309427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10494363547038061500872951 15741545320557092251309427)
              ·
                refine ⟨23612317980835638376964141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15741545320557092251309427 23612317980835638376964141)
                ·
                  refine ⟨8854619242813364391361553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23612317980835638376964141 8854619242813364391361553)
                  ·
                    refine ⟨6640964432110023293521165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8854619242813364391361553 6640964432110023293521165)
                    ·
                      refine ⟨2490361662041258735070437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6640964432110023293521165 2490361662041258735070437)
                      ·
                        rfl

theorem cell23_4849962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4849962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4849962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4849962 prefixEnd_4849962 := by exact prefixLift 4849962
  have htrace : WordTrace (prefixWord ++ tailWord_4849962) baseStart_4849962 baseEnd_4849962 := by
    simpa [prefixWord, tailWord_4849962, baseEnd_4849962] using wordTrace_append hprefix tailTrace_4849962
  have hstable : (prefixWord ++ tailWord_4849962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4849962).length < 2 ^ (prefixWord ++ tailWord_4849962).sum := by decide
  have hdescent : baseEnd_4849962 < baseStart_4849962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4849962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850015 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 1, 4, 2]
def baseStart_4850015 : Nat := 118140960795 + 4850015 * 2 ^ 59
def prefixEnd_4850015 : Nat := 4983230072969 + 3 ^ 40 * 4850015 * 2
def baseEnd_4850015 : Nat := 2490388876515947027707693

theorem tailTrace_4850015 : CollatzResearch.WordTrace tailWord_4850015 prefixEnd_4850015 2490388876515947027707693 := by
  unfold tailWord_4850015
  simp only [CollatzResearch.WordTrace]
  refine ⟨176894579524231446461455499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117929719682820964307636999 176894579524231446461455499)
  ·
    refine ⟨265341869286347169692183249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176894579524231446461455499 265341869286347169692183249)
    ·
      refine ⟨199006401964760377269137437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265341869286347169692183249 199006401964760377269137437)
      ·
        refine ⟨74627400736785141475926539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199006401964760377269137437 74627400736785141475926539)
        ·
          refine ⟨111941101105177712213889809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74627400736785141475926539 111941101105177712213889809)
          ·
            refine ⟨83955825828883284160417357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111941101105177712213889809 83955825828883284160417357)
            ·
              refine ⟨31483434685831231560156509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83955825828883284160417357 31483434685831231560156509)
              ·
                refine ⟨11806288007186711835058691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31483434685831231560156509 11806288007186711835058691)
                ·
                  refine ⟨17709432010780067752588037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11806288007186711835058691 17709432010780067752588037)
                  ·
                    refine ⟨3320518502021262703610257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17709432010780067752588037 3320518502021262703610257)
                    ·
                      refine ⟨2490388876515947027707693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3320518502021262703610257 2490388876515947027707693)
                      ·
                        rfl

theorem cell23_4850015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_4850015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850015 prefixEnd_4850015 := by exact prefixLift 4850015
  have htrace : WordTrace (prefixWord ++ tailWord_4850015) baseStart_4850015 baseEnd_4850015 := by
    simpa [prefixWord, tailWord_4850015, baseEnd_4850015] using wordTrace_append hprefix tailTrace_4850015
  have hstable : (prefixWord ++ tailWord_4850015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850015).length < 2 ^ (prefixWord ++ tailWord_4850015).sum := by decide
  have hdescent : baseEnd_4850015 < baseStart_4850015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850049 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_4850049 : Nat := 118140960795 + 4850049 * 2 ^ 59
def prefixEnd_4850049 : Nat := 4983230072969 + 3 ^ 40 * 4850049 * 2
def baseEnd_4850049 : Nat := 2490406334858199894682537

theorem tailTrace_4850049 : CollatzResearch.WordTrace tailWord_4850049 prefixEnd_4850049 2490406334858199894682537 := by
  unfold tailWord_4850049
  simp only [CollatzResearch.WordTrace]
  refine ⟨176895819606108270268193201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117930546404072180178795467 176895819606108270268193201)
  ·
    refine ⟨132671864704581202701144901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176895819606108270268193201 132671864704581202701144901)
    ·
      refine ⟨24875974632108975506464669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132671864704581202701144901 24875974632108975506464669)
      ·
        refine ⟨9328490487040865814924251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24875974632108975506464669 9328490487040865814924251)
        ·
          refine ⟨13992735730561298722386377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9328490487040865814924251 13992735730561298722386377)
          ·
            refine ⟨10494551797920974041789783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13992735730561298722386377 10494551797920974041789783)
            ·
              refine ⟨15741827696881461062684675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10494551797920974041789783 15741827696881461062684675)
              ·
                refine ⟨23612741545322191594027013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15741827696881461062684675 23612741545322191594027013)
                ·
                  refine ⟨4427389039747910923880065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23612741545322191594027013 4427389039747910923880065)
                  ·
                    refine ⟨3320541779810933192910049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4427389039747910923880065 3320541779810933192910049)
                    ·
                      refine ⟨2490406334858199894682537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3320541779810933192910049 2490406334858199894682537)
                      ·
                        rfl

theorem cell23_4850049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_4850049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850049 prefixEnd_4850049 := by exact prefixLift 4850049
  have htrace : WordTrace (prefixWord ++ tailWord_4850049) baseStart_4850049 baseEnd_4850049 := by
    simpa [prefixWord, tailWord_4850049, baseEnd_4850049] using wordTrace_append hprefix tailTrace_4850049
  have hstable : (prefixWord ++ tailWord_4850049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850049).length < 2 ^ (prefixWord ++ tailWord_4850049).sum := by decide
  have hdescent : baseEnd_4850049 < baseStart_4850049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850055 : List Nat := [1, 1, 4, 2, 2, 1, 1, 6, 5]
def baseStart_4850055 : Nat := 118140960795 + 4850055 * 2 ^ 59
def prefixEnd_4850055 : Nat := 4983230072969 + 3 ^ 40 * 4850055 * 2
def baseEnd_4850055 : Nat := 276712157304680763467501

theorem tailTrace_4850055 : CollatzResearch.WordTrace tailWord_4850055 prefixEnd_4850055 276712157304680763467501 := by
  unfold tailWord_4850055
  simp only [CollatzResearch.WordTrace]
  refine ⟨176896038444086533292911619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117930692296057688861941079 176896038444086533292911619)
  ·
    refine ⟨265344057666129799939367429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176896038444086533292911619 265344057666129799939367429)
    ·
      refine ⟨49752010812399337488631393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265344057666129799939367429 49752010812399337488631393)
      ·
        refine ⟨37314008109299503116473545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49752010812399337488631393 37314008109299503116473545)
        ·
          refine ⟨27985506081974627337355159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37314008109299503116473545 27985506081974627337355159)
          ·
            refine ⟨41978259122961941006032739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27985506081974627337355159 41978259122961941006032739)
            ·
              refine ⟨62967388684442911509049109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41978259122961941006032739 62967388684442911509049109)
              ·
                refine ⟨2951596344583261476986677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62967388684442911509049109 2951596344583261476986677)
                ·
                  refine ⟨276712157304680763467501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2951596344583261476986677 276712157304680763467501)
                  ·
                    rfl

theorem cell23_4850055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 6, 5].length) (baseStart_4850055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850055 prefixEnd_4850055 := by exact prefixLift 4850055
  have htrace : WordTrace (prefixWord ++ tailWord_4850055) baseStart_4850055 baseEnd_4850055 := by
    simpa [prefixWord, tailWord_4850055, baseEnd_4850055] using wordTrace_append hprefix tailTrace_4850055
  have hstable : (prefixWord ++ tailWord_4850055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850055).length < 2 ^ (prefixWord ++ tailWord_4850055).sum := by decide
  have hdescent : baseEnd_4850055 < baseStart_4850055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850070 : List Nat := [5, 3, 1, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_4850070 : Nat := 118140960795 + 4850070 * 2 ^ 59
def prefixEnd_4850070 : Nat := 4983230072969 + 3 ^ 40 * 4850070 * 2
def baseEnd_4850070 : Nat := 2490417117951944312519941

theorem tailTrace_4850070 : CollatzResearch.WordTrace tailWord_4850070 prefixEnd_4850070 2490417117951944312519941 := by
  unfold tailWord_4850070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11056036596189511928419229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117931057026021460569805109 11056036596189511928419229)
  ·
    refine ⟨4146013723571066973157211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11056036596189511928419229 4146013723571066973157211)
    ·
      refine ⟨6219020585356600459735817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4146013723571066973157211 6219020585356600459735817)
      ·
        refine ⟨4664265439017450344801863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6219020585356600459735817 4664265439017450344801863)
        ·
          refine ⟨6996398158526175517202795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664265439017450344801863 6996398158526175517202795)
          ·
            refine ⟨10494597237789263275804193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6996398158526175517202795 10494597237789263275804193)
            ·
              refine ⟨7870947928341947456853145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10494597237789263275804193 7870947928341947456853145)
              ·
                refine ⟨5903210946256460592639859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7870947928341947456853145 5903210946256460592639859)
                ·
                  refine ⟨8854816419384690888959789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5903210946256460592639859 8854816419384690888959789)
                  ·
                    refine ⟨3320556157269259083359921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8854816419384690888959789 3320556157269259083359921)
                    ·
                      refine ⟨2490417117951944312519941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3320556157269259083359921 2490417117951944312519941)
                      ·
                        rfl

theorem cell23_4850070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_4850070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850070 prefixEnd_4850070 := by exact prefixLift 4850070
  have htrace : WordTrace (prefixWord ++ tailWord_4850070) baseStart_4850070 baseEnd_4850070 := by
    simpa [prefixWord, tailWord_4850070, baseEnd_4850070] using wordTrace_append hprefix tailTrace_4850070
  have hstable : (prefixWord ++ tailWord_4850070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850070).length < 2 ^ (prefixWord ++ tailWord_4850070).sum := by decide
  have hdescent : baseEnd_4850070 < baseStart_4850070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850105 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 4, 1, 4]
def baseStart_4850105 : Nat := 118140960795 + 4850105 * 2 ^ 59
def prefixEnd_4850105 : Nat := 4983230072969 + 3 ^ 40 * 4850105 * 2
def baseEnd_4850105 : Nat := 2490435089774851675582279

theorem tailTrace_4850105 : CollatzResearch.WordTrace tailWord_4850105 prefixEnd_4850105 2490435089774851675582279 := by
  unfold tailWord_4850105
  simp only [CollatzResearch.WordTrace]
  refine ⟨176897862093905391832231769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117931908062603594554821179 176897862093905391832231769)
  ·
    refine ⟨132673396570429043874173827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176897862093905391832231769 132673396570429043874173827)
    ·
      refine ⟨199010094855643565811260741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132673396570429043874173827 199010094855643565811260741)
      ·
        refine ⟨37314392785433168589611389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199010094855643565811260741 37314392785433168589611389)
        ·
          refine ⟨13992897294537438221104271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37314392785433168589611389 13992897294537438221104271)
          ·
            refine ⟨20989345941806157331656407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13992897294537438221104271 20989345941806157331656407)
            ·
              refine ⟨31484018912709235997484611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20989345941806157331656407 31484018912709235997484611)
              ·
                refine ⟨47226028369063853996226917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31484018912709235997484611 47226028369063853996226917)
                ·
                  refine ⟨8854880319199472624292547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47226028369063853996226917 8854880319199472624292547)
                  ·
                    refine ⟨13282320478799208936438821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8854880319199472624292547 13282320478799208936438821)
                    ·
                      refine ⟨2490435089774851675582279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13282320478799208936438821 2490435089774851675582279)
                      ·
                        rfl

theorem cell23_4850105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_4850105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850105 prefixEnd_4850105 := by exact prefixLift 4850105
  have htrace : WordTrace (prefixWord ++ tailWord_4850105) baseStart_4850105 baseEnd_4850105 := by
    simpa [prefixWord, tailWord_4850105, baseEnd_4850105] using wordTrace_append hprefix tailTrace_4850105
  have hstable : (prefixWord ++ tailWord_4850105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850105).length < 2 ^ (prefixWord ++ tailWord_4850105).sum := by decide
  have hdescent : baseEnd_4850105 < baseStart_4850105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850148 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_4850148 : Nat := 118140960795 + 4850148 * 2 ^ 59
def prefixEnd_4850148 : Nat := 4983230072969 + 3 ^ 40 * 4850148 * 2
def baseEnd_4850148 : Nat := 2490457169442995007344581

theorem tailTrace_4850148 : CollatzResearch.WordTrace tailWord_4850148 prefixEnd_4850148 2490457169442995007344581 := by
  unfold tailWord_4850148
  simp only [CollatzResearch.WordTrace]
  refine ⟨88449715216374805088023549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117932953621833073450698065 88449715216374805088023549)
  ·
    refine ⟨33168643206140551908008831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88449715216374805088023549 33168643206140551908008831)
    ·
      refine ⟨49752964809210827862013247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33168643206140551908008831 49752964809210827862013247)
      ·
        refine ⟨74629447213816241793019871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49752964809210827862013247 74629447213816241793019871)
        ·
          refine ⟨111944170820724362689529807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74629447213816241793019871 111944170820724362689529807)
          ·
            refine ⟨167916256231086544034294711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111944170820724362689529807 167916256231086544034294711)
            ·
              refine ⟨251874384346629816051442067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167916256231086544034294711 251874384346629816051442067)
              ·
                refine ⟨377811576519944724077163101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251874384346629816051442067 377811576519944724077163101)
                ·
                  refine ⟨141679341194979271528936163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377811576519944724077163101 141679341194979271528936163)
                  ·
                    refine ⟨212519011792468907293404245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 141679341194979271528936163 212519011792468907293404245)
                    ·
                      refine ⟨2490457169442995007344581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 212519011792468907293404245 2490457169442995007344581)
                      ·
                        rfl

theorem cell23_4850148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_4850148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850148 prefixEnd_4850148 := by exact prefixLift 4850148
  have htrace : WordTrace (prefixWord ++ tailWord_4850148) baseStart_4850148 baseEnd_4850148 := by
    simpa [prefixWord, tailWord_4850148, baseEnd_4850148] using wordTrace_append hprefix tailTrace_4850148
  have hstable : (prefixWord ++ tailWord_4850148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850148).length < 2 ^ (prefixWord ++ tailWord_4850148).sum := by decide
  have hdescent : baseEnd_4850148 < baseStart_4850148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850172 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_4850172 : Nat := 118140960795 + 4850172 * 2 ^ 59
def prefixEnd_4850172 : Nat := 4983230072969 + 3 ^ 40 * 4850172 * 2
def baseEnd_4850172 : Nat := 2490469492978702913444471

theorem tailTrace_4850172 : CollatzResearch.WordTrace tailWord_4850172 prefixEnd_4850172 2490469492978702913444471 := by
  unfold tailWord_4850172
  simp only [CollatzResearch.WordTrace]
  refine ⟨88450152892331331137460385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117933537189775108183280513 88450152892331331137460385)
  ·
    refine ⟨66337614669248498353095289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88450152892331331137460385 66337614669248498353095289)
    ·
      refine ⟨49753211001936373764821467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66337614669248498353095289 49753211001936373764821467)
      ·
        refine ⟨74629816502904560647232201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49753211001936373764821467 74629816502904560647232201)
        ·
          refine ⟨55972362377178420485424151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74629816502904560647232201 55972362377178420485424151)
          ·
            refine ⟨83958543565767630728136227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55972362377178420485424151 83958543565767630728136227)
            ·
              refine ⟨125937815348651446092204341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83958543565767630728136227 125937815348651446092204341)
              ·
                refine ⟨11806670188936073071144157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125937815348651446092204341 11806670188936073071144157)
                ·
                  refine ⟨4427501320851027401679059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11806670188936073071144157 4427501320851027401679059)
                  ·
                    refine ⟨6641251981276541102518589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4427501320851027401679059 6641251981276541102518589)
                    ·
                      refine ⟨2490469492978702913444471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6641251981276541102518589 2490469492978702913444471)
                      ·
                        rfl

theorem cell23_4850172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_4850172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850172 prefixEnd_4850172 := by exact prefixLift 4850172
  have htrace : WordTrace (prefixWord ++ tailWord_4850172) baseStart_4850172 baseEnd_4850172 := by
    simpa [prefixWord, tailWord_4850172, baseEnd_4850172] using wordTrace_append hprefix tailTrace_4850172
  have hstable : (prefixWord ++ tailWord_4850172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850172).length < 2 ^ (prefixWord ++ tailWord_4850172).sum := by decide
  have hdescent : baseEnd_4850172 < baseStart_4850172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850195 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 4]
def baseStart_4850195 : Nat := 118140960795 + 4850195 * 2 ^ 59
def prefixEnd_4850195 : Nat := 4983230072969 + 3 ^ 40 * 4850195 * 2
def baseEnd_4850195 : Nat := 2490481303033756323456865

theorem tailTrace_4850195 : CollatzResearch.WordTrace tailWord_4850195 prefixEnd_4850195 2490481303033756323456865 := by
  unfold tailWord_4850195
  simp only [CollatzResearch.WordTrace]
  refine ⟨176901144663579337203008039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117934096442386224802005359 176901144663579337203008039)
  ·
    refine ⟨265351716995369005804512059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176901144663579337203008039 265351716995369005804512059)
    ·
      refine ⟨398027575493053508706768089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265351716995369005804512059 398027575493053508706768089)
      ·
        refine ⟨298520681619790131530076067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398027575493053508706768089 298520681619790131530076067)
        ·
          refine ⟨447781022429685197295114101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298520681619790131530076067 447781022429685197295114101)
          ·
            refine ⟨41979470852782987246416947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 447781022429685197295114101 41979470852782987246416947)
            ·
              refine ⟨62969206279174480869625421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41979470852782987246416947 62969206279174480869625421)
              ·
                refine ⟨23613452354690430326109533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62969206279174480869625421 23613452354690430326109533)
                ·
                  refine ⟨8855044633008911372291075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23613452354690430326109533 8855044633008911372291075)
                  ·
                    refine ⟨13282566949513367058436613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8855044633008911372291075 13282566949513367058436613)
                    ·
                      refine ⟨2490481303033756323456865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13282566949513367058436613 2490481303033756323456865)
                      ·
                        rfl

theorem cell23_4850195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_4850195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850195 prefixEnd_4850195 := by exact prefixLift 4850195
  have htrace : WordTrace (prefixWord ++ tailWord_4850195) baseStart_4850195 baseEnd_4850195 := by
    simpa [prefixWord, tailWord_4850195, baseEnd_4850195] using wordTrace_append hprefix tailTrace_4850195
  have hstable : (prefixWord ++ tailWord_4850195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850195).length < 2 ^ (prefixWord ++ tailWord_4850195).sum := by decide
  have hdescent : baseEnd_4850195 < baseStart_4850195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850225 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 3, 2, 4]
def baseStart_4850225 : Nat := 118140960795 + 4850225 * 2 ^ 59
def prefixEnd_4850225 : Nat := 4983230072969 + 3 ^ 40 * 4850225 * 2
def baseEnd_4850225 : Nat := 2490496707453391206081727

theorem tailTrace_4850225 : CollatzResearch.WordTrace tailWord_4850225 prefixEnd_4850225 2490496707453391206081727 := by
  unfold tailWord_4850225
  simp only [CollatzResearch.WordTrace]
  refine ⟨176902238853470652326600129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117934825902313768217733419 176902238853470652326600129)
  ·
    refine ⟨132676679140102989244950097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176902238853470652326600129 132676679140102989244950097)
    ·
      refine ⟨99507509355077241933712573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132676679140102989244950097 99507509355077241933712573)
      ·
        refine ⟨37315316008153965725142215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99507509355077241933712573 37315316008153965725142215)
        ·
          refine ⟨55972974012230948587713323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37315316008153965725142215 55972974012230948587713323)
          ·
            refine ⟨83959461018346422881569985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55972974012230948587713323 83959461018346422881569985)
            ·
              refine ⟨62969595763759817161177489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83959461018346422881569985 62969595763759817161177489)
              ·
                refine ⟨47227196822819862870883117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62969595763759817161177489 47227196822819862870883117)
                ·
                  refine ⟨17710198808557448576581169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47227196822819862870883117 17710198808557448576581169)
                  ·
                    refine ⟨13282649106418086432435877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17710198808557448576581169 13282649106418086432435877)
                    ·
                      refine ⟨2490496707453391206081727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13282649106418086432435877 2490496707453391206081727)
                      ·
                        rfl

theorem cell23_4850225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_4850225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850225 prefixEnd_4850225 := by exact prefixLift 4850225
  have htrace : WordTrace (prefixWord ++ tailWord_4850225) baseStart_4850225 baseEnd_4850225 := by
    simpa [prefixWord, tailWord_4850225, baseEnd_4850225] using wordTrace_append hprefix tailTrace_4850225
  have hstable : (prefixWord ++ tailWord_4850225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850225).length < 2 ^ (prefixWord ++ tailWord_4850225).sum := by decide
  have hdescent : baseEnd_4850225 < baseStart_4850225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850239 : List Nat := [1, 1, 2, 2, 3, 2, 5, 1, 2, 4]
def baseStart_4850239 : Nat := 118140960795 + 4850239 * 2 ^ 59
def prefixEnd_4850239 : Nat := 4983230072969 + 3 ^ 40 * 4850239 * 2
def baseEnd_4850239 : Nat := 830167965394184717102221

theorem tailTrace_4850239 : CollatzResearch.WordTrace tailWord_4850239 prefixEnd_4850239 830167965394184717102221 := by
  unfold tailWord_4850239
  simp only [CollatzResearch.WordTrace]
  refine ⟨176902749475419932717609771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117935166316946621811739847 176902749475419932717609771)
  ·
    refine ⟨265354124213129899076414657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176902749475419932717609771 265354124213129899076414657)
    ·
      refine ⟨199015593159847424307310993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265354124213129899076414657 199015593159847424307310993)
      ·
        refine ⟨149261694869885568230483245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199015593159847424307310993 149261694869885568230483245)
        ·
          refine ⟨55973135576207088086431217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149261694869885568230483245 55973135576207088086431217)
          ·
            refine ⟨41979851682155316064823413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55973135576207088086431217 41979851682155316064823413)
            ·
              refine ⟨3935611095202060881077195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41979851682155316064823413 3935611095202060881077195)
              ·
                refine ⟨5903416642803091321615793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935611095202060881077195 5903416642803091321615793)
                ·
                  refine ⟨4427562482102318491211845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5903416642803091321615793 4427562482102318491211845)
                  ·
                    refine ⟨830167965394184717102221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4427562482102318491211845 830167965394184717102221)
                    ·
                      rfl

theorem cell23_4850239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 2, 4].length) (baseStart_4850239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850239 prefixEnd_4850239 := by exact prefixLift 4850239
  have htrace : WordTrace (prefixWord ++ tailWord_4850239) baseStart_4850239 baseEnd_4850239 := by
    simpa [prefixWord, tailWord_4850239, baseEnd_4850239] using wordTrace_append hprefix tailTrace_4850239
  have hstable : (prefixWord ++ tailWord_4850239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850239).length < 2 ^ (prefixWord ++ tailWord_4850239).sum := by decide
  have hdescent : baseEnd_4850239 < baseStart_4850239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850246 : List Nat := [6, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_4850246 : Nat := 118140960795 + 4850246 * 2 ^ 59
def prefixEnd_4850246 : Nat := 4983230072969 + 3 ^ 40 * 4850246 * 2
def baseEnd_4850246 : Nat := 2490507490547135623919131

theorem tailTrace_4850246 : CollatzResearch.WordTrace tailWord_4850246 prefixEnd_4850246 2490507490547135623919131 := by
  unfold tailWord_4850246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528218899574830403534831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 117935336524263048608743061 5528218899574830403534831)
  ·
    refine ⟨8292328349362245605302247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5528218899574830403534831 8292328349362245605302247)
    ·
      refine ⟨12438492524043368407953371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8292328349362245605302247 12438492524043368407953371)
      ·
        refine ⟨18657738786065052611930057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12438492524043368407953371 18657738786065052611930057)
        ·
          refine ⟨13993304089548789458947543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18657738786065052611930057 13993304089548789458947543)
          ·
            refine ⟨20989956134323184188421315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13993304089548789458947543 20989956134323184188421315)
            ·
              refine ⟨31484934201484776282631973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20989956134323184188421315 31484934201484776282631973)
              ·
                refine ⟨5903425162778395552993495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31484934201484776282631973 5903425162778395552993495)
                ·
                  refine ⟨8855137744167593329490243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5903425162778395552993495 8855137744167593329490243)
                  ·
                    refine ⟨13282706616251389994235365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8855137744167593329490243 13282706616251389994235365)
                    ·
                      refine ⟨2490507490547135623919131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13282706616251389994235365 2490507490547135623919131)
                      ·
                        rfl

theorem cell23_4850246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_4850246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850246 prefixEnd_4850246 := by exact prefixLift 4850246
  have htrace : WordTrace (prefixWord ++ tailWord_4850246) baseStart_4850246 baseEnd_4850246 := by
    simpa [prefixWord, tailWord_4850246, baseEnd_4850246] using wordTrace_append hprefix tailTrace_4850246
  have hstable : (prefixWord ++ tailWord_4850246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850246).length < 2 ^ (prefixWord ++ tailWord_4850246).sum := by decide
  have hdescent : baseEnd_4850246 < baseStart_4850246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850275 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 5]
def baseStart_4850275 : Nat := 118140960795 + 4850275 * 2 ^ 59
def prefixEnd_4850275 : Nat := 4983230072969 + 3 ^ 40 * 4850275 * 2
def baseEnd_4850275 : Nat := 2490522381486116010456497

theorem tailTrace_4850275 : CollatzResearch.WordTrace tailWord_4850275 prefixEnd_4850275 2490522381486116010456497 := by
  unfold tailWord_4850275
  simp only [CollatzResearch.WordTrace]
  refine ⟨176904062503289510865920279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117936041668859673910613519 176904062503289510865920279)
  ·
    refine ⟨265356093754934266298880419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176904062503289510865920279 265356093754934266298880419)
    ·
      refine ⟨398034140632401399448320629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265356093754934266298880419 398034140632401399448320629)
      ·
        refine ⟨37315700684287631198280059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 398034140632401399448320629 37315700684287631198280059)
        ·
          refine ⟨55973551026431446797420089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37315700684287631198280059 55973551026431446797420089)
          ·
            refine ⟨41980163269823585098065067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55973551026431446797420089 41980163269823585098065067)
            ·
              refine ⟨62970244904735377647097601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41980163269823585098065067 62970244904735377647097601)
              ·
                refine ⟨47227683678551533235323201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62970244904735377647097601 47227683678551533235323201)
                ·
                  refine ⟨35420762758913649926492401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47227683678551533235323201 35420762758913649926492401)
                  ·
                    refine ⟨26565572069185237444869301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35420762758913649926492401 26565572069185237444869301)
                    ·
                      refine ⟨2490522381486116010456497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26565572069185237444869301 2490522381486116010456497)
                      ·
                        rfl

theorem cell23_4850275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_4850275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850275 prefixEnd_4850275 := by exact prefixLift 4850275
  have htrace : WordTrace (prefixWord ++ tailWord_4850275) baseStart_4850275 baseEnd_4850275 := by
    simpa [prefixWord, tailWord_4850275, baseEnd_4850275] using wordTrace_append hprefix tailTrace_4850275
  have hstable : (prefixWord ++ tailWord_4850275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850275).length < 2 ^ (prefixWord ++ tailWord_4850275).sum := by decide
  have hdescent : baseEnd_4850275 < baseStart_4850275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850279 : List Nat := [1, 1, 5, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_4850279 : Nat := 118140960795 + 4850279 * 2 ^ 59
def prefixEnd_4850279 : Nat := 4983230072969 + 3 ^ 40 * 4850279 * 2
def baseEnd_4850279 : Nat := 2490524435408733994806479

theorem tailTrace_4850279 : CollatzResearch.WordTrace tailWord_4850279 prefixEnd_4850279 2490524435408733994806479 := by
  unfold tailWord_4850279
  simp only [CollatzResearch.WordTrace]
  refine ⟨176904208395275019549065891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117936138930183346366043927 176904208395275019549065891)
  ·
    refine ⟨265356312592912529323598837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176904208395275019549065891 265356312592912529323598837)
    ·
      refine ⟨24877154305585549624087391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 265356312592912529323598837 24877154305585549624087391)
      ·
        refine ⟨37315731458378324436131087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24877154305585549624087391 37315731458378324436131087)
        ·
          refine ⟨55973597187567486654196631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37315731458378324436131087 55973597187567486654196631)
          ·
            refine ⟨83960395781351229981294947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55973597187567486654196631 83960395781351229981294947)
            ·
              refine ⟨125940593672026844971942421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83960395781351229981294947 125940593672026844971942421)
              ·
                refine ⟨5903465328376258358059801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 125940593672026844971942421 5903465328376258358059801)
                ·
                  refine ⟨4427598996282193768544851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5903465328376258358059801 4427598996282193768544851)
                  ·
                    refine ⟨6641398494423290652817277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4427598996282193768544851 6641398494423290652817277)
                    ·
                      refine ⟨2490524435408733994806479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6641398494423290652817277 2490524435408733994806479)
                      ·
                        rfl

theorem cell23_4850279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_4850279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850279 prefixEnd_4850279 := by exact prefixLift 4850279
  have htrace : WordTrace (prefixWord ++ tailWord_4850279) baseStart_4850279 baseEnd_4850279 := by
    simpa [prefixWord, tailWord_4850279, baseEnd_4850279] using wordTrace_append hprefix tailTrace_4850279
  have hstable : (prefixWord ++ tailWord_4850279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850279).length < 2 ^ (prefixWord ++ tailWord_4850279).sum := by decide
  have hdescent : baseEnd_4850279 < baseStart_4850279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850280 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_4850280 : Nat := 118140960795 + 4850280 * 2 ^ 59
def prefixEnd_4850280 : Nat := 4983230072969 + 3 ^ 40 * 4850280 * 2
def baseEnd_4850280 : Nat := 2490524948889388490893975

theorem tailTrace_4850280 : CollatzResearch.WordTrace tailWord_4850280 prefixEnd_4850280 2490524948889388490893975 := by
  unfold tailWord_4850280
  simp only [CollatzResearch.WordTrace]
  refine ⟨88452122434135698359926147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117936163245514264479901529 88452122434135698359926147)
  ·
    refine ⟨132678183651203547539889221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88452122434135698359926147 132678183651203547539889221)
    ·
      refine ⟨24877159434600665163729229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132678183651203547539889221 24877159434600665163729229)
      ·
        refine ⟨9328934787975249436398461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24877159434600665163729229 9328934787975249436398461)
        ·
          refine ⟨3498350545490718538649423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9328934787975249436398461 3498350545490718538649423)
          ·
            refine ⟨5247525818236077807974135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3498350545490718538649423 5247525818236077807974135)
            ·
              refine ⟨7871288727354116711961203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5247525818236077807974135 7871288727354116711961203)
              ·
                refine ⟨11806933091031175067941805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7871288727354116711961203 11806933091031175067941805)
                ·
                  refine ⟨4427599909136690650478177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11806933091031175067941805 4427599909136690650478177)
                  ·
                    refine ⟨3320699931852517987858633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4427599909136690650478177 3320699931852517987858633)
                    ·
                      refine ⟨2490524948889388490893975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3320699931852517987858633 2490524948889388490893975)
                      ·
                        rfl

theorem cell23_4850280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_4850280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850280 prefixEnd_4850280 := by exact prefixLift 4850280
  have htrace : WordTrace (prefixWord ++ tailWord_4850280) baseStart_4850280 baseEnd_4850280 := by
    simpa [prefixWord, tailWord_4850280, baseEnd_4850280] using wordTrace_append hprefix tailTrace_4850280
  have hstable : (prefixWord ++ tailWord_4850280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850280).length < 2 ^ (prefixWord ++ tailWord_4850280).sum := by decide
  have hdescent : baseEnd_4850280 < baseStart_4850280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850295 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 2, 6]
def baseStart_4850295 : Nat := 118140960795 + 4850295 * 2 ^ 59
def prefixEnd_4850295 : Nat := 4983230072969 + 3 ^ 40 * 4850295 * 2
def baseEnd_4850295 : Nat := 830177550366401977402135

theorem tailTrace_4850295 : CollatzResearch.WordTrace tailWord_4850295 prefixEnd_4850295 830177550366401977402135 := by
  unfold tailWord_4850295
  simp only [CollatzResearch.WordTrace]
  refine ⟨176904791963217054281648339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117936527975478036187765559 176904791963217054281648339)
  ·
    refine ⟨265357187944825581422472509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176904791963217054281648339 265357187944825581422472509)
    ·
      refine ⟨99508945479309593033427191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265357187944825581422472509 99508945479309593033427191)
      ·
        refine ⟨149263418218964389550140787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99508945479309593033427191 149263418218964389550140787)
        ·
          refine ⟨223895127328446584325211181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149263418218964389550140787 223895127328446584325211181)
          ·
            refine ⟨83960672748167469121954193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223895127328446584325211181 83960672748167469121954193)
            ·
              refine ⟨62970504561125601841465645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83960672748167469121954193 62970504561125601841465645)
              ·
                refine ⟨23613939210422100690549617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62970504561125601841465645 23613939210422100690549617)
                ·
                  refine ⟨17710454407816575517912213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23613939210422100690549617 17710454407816575517912213)
                  ·
                    refine ⟨830177550366401977402135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17710454407816575517912213 830177550366401977402135)
                    ·
                      rfl

theorem cell23_4850295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 6].length) (baseStart_4850295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850295 prefixEnd_4850295 := by exact prefixLift 4850295
  have htrace : WordTrace (prefixWord ++ tailWord_4850295) baseStart_4850295 baseEnd_4850295 := by
    simpa [prefixWord, tailWord_4850295, baseEnd_4850295] using wordTrace_append hprefix tailTrace_4850295
  have hstable : (prefixWord ++ tailWord_4850295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850295).length < 2 ^ (prefixWord ++ tailWord_4850295).sum := by decide
  have hdescent : baseEnd_4850295 < baseStart_4850295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850315 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 4]
def baseStart_4850315 : Nat := 118140960795 + 4850315 * 2 ^ 59
def prefixEnd_4850315 : Nat := 4983230072969 + 3 ^ 40 * 4850315 * 2
def baseEnd_4850315 : Nat := 2490542920712295853956313

theorem tailTrace_4850315 : CollatzResearch.WordTrace tailWord_4850315 prefixEnd_4850315 2490542920712295853956313 := by
  unfold tailWord_4850315
  simp only [CollatzResearch.WordTrace]
  refine ⟨176905521423144597697376399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117937014282096398464917599 176905521423144597697376399)
  ·
    refine ⟨265358282134716896546064599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176905521423144597697376399 265358282134716896546064599)
    ·
      refine ⟨398037423202075344819096899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265358282134716896546064599 398037423202075344819096899)
      ·
        refine ⟨597056134803113017228645349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398037423202075344819096899 597056134803113017228645349)
        ·
          refine ⟨111948025275583690730371003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 597056134803113017228645349 111948025275583690730371003)
          ·
            refine ⟨167922037913375536095556505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111948025275583690730371003 167922037913375536095556505)
            ·
              refine ⟨125941528435031652071667379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167922037913375536095556505 125941528435031652071667379)
              ·
                refine ⟨188912292652547478107501069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125941528435031652071667379 188912292652547478107501069)
                ·
                  refine ⟨70842109744705304290312901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188912292652547478107501069 70842109744705304290312901)
                  ·
                    refine ⟨13282895577132244554433669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70842109744705304290312901 13282895577132244554433669)
                    ·
                      refine ⟨2490542920712295853956313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13282895577132244554433669 2490542920712295853956313)
                      ·
                        rfl

theorem cell23_4850315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 4].length) (baseStart_4850315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850315 prefixEnd_4850315 := by exact prefixLift 4850315
  have htrace : WordTrace (prefixWord ++ tailWord_4850315) baseStart_4850315 baseEnd_4850315 := by
    simpa [prefixWord, tailWord_4850315, baseEnd_4850315] using wordTrace_append hprefix tailTrace_4850315
  have hstable : (prefixWord ++ tailWord_4850315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850315).length < 2 ^ (prefixWord ++ tailWord_4850315).sum := by decide
  have hdescent : baseEnd_4850315 < baseStart_4850315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850346 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 2, 6]
def baseStart_4850346 : Nat := 118140960795 + 4850346 * 2 ^ 59
def prefixEnd_4850346 : Nat := 4983230072969 + 3 ^ 40 * 4850346 * 2
def baseEnd_4850346 : Nat := 830186279537528410889557

theorem tailTrace_4850346 : CollatzResearch.WordTrace tailWord_4850346 prefixEnd_4850346 830186279537528410889557 := by
  unfold tailWord_4850346
  simp only [CollatzResearch.WordTrace]
  refine ⟨44226663021508072497938723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117937768057354859994503261 44226663021508072497938723)
  ·
    refine ⟨66339994532262108746908085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44226663021508072497938723 66339994532262108746908085)
    ·
      refine ⟨6219374487399572695022633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66339994532262108746908085 6219374487399572695022633)
      ·
        refine ⟨4664530865549679521266975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6219374487399572695022633 4664530865549679521266975)
        ·
          refine ⟨6996796298324519281900463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664530865549679521266975 6996796298324519281900463)
          ·
            refine ⟨10495194447486778922850695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6996796298324519281900463 10495194447486778922850695)
            ·
              refine ⟨15742791671230168384276043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10495194447486778922850695 15742791671230168384276043)
              ·
                refine ⟨23614187506845252576414065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15742791671230168384276043 23614187506845252576414065)
                ·
                  refine ⟨17710640630133939432310549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23614187506845252576414065 17710640630133939432310549)
                  ·
                    refine ⟨830186279537528410889557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17710640630133939432310549 830186279537528410889557)
                    ·
                      rfl

theorem cell23_4850346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_4850346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850346 prefixEnd_4850346 := by exact prefixLift 4850346
  have htrace : WordTrace (prefixWord ++ tailWord_4850346) baseStart_4850346 baseEnd_4850346 := by
    simpa [prefixWord, tailWord_4850346, baseEnd_4850346] using wordTrace_append hprefix tailTrace_4850346
  have hstable : (prefixWord ++ tailWord_4850346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850346).length < 2 ^ (prefixWord ++ tailWord_4850346).sum := by decide
  have hdescent : baseEnd_4850346 < baseStart_4850346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850349 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_4850349 : Nat := 118140960795 + 4850349 * 2 ^ 59
def prefixEnd_4850349 : Nat := 4983230072969 + 3 ^ 40 * 4850349 * 2
def baseEnd_4850349 : Nat := 2490560379054548720931157

theorem tailTrace_4850349 : CollatzResearch.WordTrace tailWord_4850349 prefixEnd_4850349 2490560379054548720931157 := by
  unfold tailWord_4850349
  simp only [CollatzResearch.WordTrace]
  refine ⟨176906761505021421504114101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117937841003347614336076067 176906761505021421504114101)
  ·
    refine ⟨16585008891095758266010697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176906761505021421504114101 16585008891095758266010697)
    ·
      refine ⟨12438756668321818699508023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16585008891095758266010697 12438756668321818699508023)
      ·
        refine ⟨18658135002482728049262035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12438756668321818699508023 18658135002482728049262035)
        ·
          refine ⟨27987202503724092073893053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18658135002482728049262035 27987202503724092073893053)
          ·
            refine ⟨10495200938896534527709895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27987202503724092073893053 10495200938896534527709895)
            ·
              refine ⟨15742801408344801791564843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10495200938896534527709895 15742801408344801791564843)
              ·
                refine ⟨23614202112517202687347265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15742801408344801791564843 23614202112517202687347265)
                ·
                  refine ⟨17710651584387902015510449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23614202112517202687347265 17710651584387902015510449)
                  ·
                    refine ⟨13282988688290926511632837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17710651584387902015510449 13282988688290926511632837)
                    ·
                      refine ⟨2490560379054548720931157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13282988688290926511632837 2490560379054548720931157)
                      ·
                        rfl

theorem cell23_4850349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_4850349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850349 prefixEnd_4850349 := by exact prefixLift 4850349
  have htrace : WordTrace (prefixWord ++ tailWord_4850349) baseStart_4850349 baseEnd_4850349 := by
    simpa [prefixWord, tailWord_4850349, baseEnd_4850349] using wordTrace_append hprefix tailTrace_4850349
  have hstable : (prefixWord ++ tailWord_4850349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850349).length < 2 ^ (prefixWord ++ tailWord_4850349).sum := by decide
  have hdescent : baseEnd_4850349 < baseStart_4850349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850353 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 1, 4, 2]
def baseStart_4850353 : Nat := 118140960795 + 4850353 * 2 ^ 59
def prefixEnd_4850353 : Nat := 4983230072969 + 3 ^ 40 * 4850353 * 2
def baseEnd_4850353 : Nat := 2490562432977166705281139

theorem tailTrace_4850353 : CollatzResearch.WordTrace tailWord_4850353 prefixEnd_4850353 2490562432977166705281139 := by
  unfold tailWord_4850353
  simp only [CollatzResearch.WordTrace]
  refine ⟨176906907397006930187259713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117937938264671286791506475 176906907397006930187259713)
  ·
    refine ⟨132680180547755197640444785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176906907397006930187259713 132680180547755197640444785)
    ·
      refine ⟨99510135410816398230333589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132680180547755197640444785 99510135410816398230333589)
      ·
        refine ⟨4664537597382018667046887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99510135410816398230333589 4664537597382018667046887)
        ·
          refine ⟨6996806396073028000570331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664537597382018667046887 6996806396073028000570331)
          ·
            refine ⟨10495209594109542000855497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6996806396073028000570331 10495209594109542000855497)
            ·
              refine ⟨7871407195582156500641623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10495209594109542000855497 7871407195582156500641623)
              ·
                refine ⟨11807110793373234750962435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7871407195582156500641623 11807110793373234750962435)
                ·
                  refine ⟨17710666190059852126443653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11807110793373234750962435 17710666190059852126443653)
                  ·
                    refine ⟨3320749910636222273708185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17710666190059852126443653 3320749910636222273708185)
                    ·
                      refine ⟨2490562432977166705281139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3320749910636222273708185 2490562432977166705281139)
                      ·
                        rfl

theorem cell23_4850353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_4850353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850353 prefixEnd_4850353 := by exact prefixLift 4850353
  have htrace : WordTrace (prefixWord ++ tailWord_4850353) baseStart_4850353 baseEnd_4850353 := by
    simpa [prefixWord, tailWord_4850353, baseEnd_4850353] using wordTrace_append hprefix tailTrace_4850353
  have hstable : (prefixWord ++ tailWord_4850353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850353).length < 2 ^ (prefixWord ++ tailWord_4850353).sum := by decide
  have hdescent : baseEnd_4850353 < baseStart_4850353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850374 : List Nat := [6, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_4850374 : Nat := 118140960795 + 4850374 * 2 ^ 59
def prefixEnd_4850374 : Nat := 4983230072969 + 3 ^ 40 * 4850374 * 2
def baseEnd_4850374 : Nat := 2490573216070911123118543

theorem tailTrace_4850374 : CollatzResearch.WordTrace tailWord_4850374 prefixEnd_4850374 2490573216070911123118543 := by
  unfold tailWord_4850374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528364791560339086680443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 117938448886620567182516117 5528364791560339086680443)
  ·
    refine ⟨8292547187340508630020665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5528364791560339086680443 8292547187340508630020665)
    ·
      refine ⟨6219410390505381472515499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8292547187340508630020665 6219410390505381472515499)
      ·
        refine ⟨9329115585758072208773249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6219410390505381472515499 9329115585758072208773249)
        ·
          refine ⟨6996836689318554156579937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9329115585758072208773249 6996836689318554156579937)
          ·
            refine ⟨5247627516988915617434953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6996836689318554156579937 5247627516988915617434953)
            ·
              refine ⟨3935720637741686713076215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5247627516988915617434953 3935720637741686713076215)
              ·
                refine ⟨5903580956612530069614323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935720637741686713076215 5903580956612530069614323)
                ·
                  refine ⟨8855371434918795104421485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5903580956612530069614323 8855371434918795104421485)
                  ·
                    refine ⟨3320764288094548164158057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8855371434918795104421485 3320764288094548164158057)
                    ·
                      refine ⟨2490573216070911123118543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3320764288094548164158057 2490573216070911123118543)
                      ·
                        rfl

theorem cell23_4850374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_4850374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850374 prefixEnd_4850374 := by exact prefixLift 4850374
  have htrace : WordTrace (prefixWord ++ tailWord_4850374) baseStart_4850374 baseEnd_4850374 := by
    simpa [prefixWord, tailWord_4850374, baseEnd_4850374] using wordTrace_append hprefix tailTrace_4850374
  have hstable : (prefixWord ++ tailWord_4850374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850374).length < 2 ^ (prefixWord ++ tailWord_4850374).sum := by decide
  have hdescent : baseEnd_4850374 < baseStart_4850374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850409 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 2, 4, 2]
def baseStart_4850409 : Nat := 118140960795 + 4850409 * 2 ^ 59
def prefixEnd_4850409 : Nat := 4983230072969 + 3 ^ 40 * 4850409 * 2
def baseEnd_4850409 : Nat := 2490591187893818486180881

theorem tailTrace_4850409 : CollatzResearch.WordTrace tailWord_4850409 prefixEnd_4850409 2490591187893818486180881 := by
  unfold tailWord_4850409
  simp only [CollatzResearch.WordTrace]
  refine ⟨176908949884804051751298281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117939299923202701167532187 176908949884804051751298281)
  ·
    refine ⟨132681712413603038813473711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176908949884804051751298281 132681712413603038813473711)
    ·
      refine ⟨199022568620404558220210567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132681712413603038813473711 199022568620404558220210567)
      ·
        refine ⟨298533852930606837330315851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199022568620404558220210567 298533852930606837330315851)
        ·
          refine ⟨447800779395910255995473777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298533852930606837330315851 447800779395910255995473777)
          ·
            refine ⟨335850584546932691996605333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447800779395910255995473777 335850584546932691996605333)
            ·
              refine ⟨15742996150637469937340875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 335850584546932691996605333 15742996150637469937340875)
              ·
                refine ⟨23614494225956204906011313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15742996150637469937340875 23614494225956204906011313)
                ·
                  refine ⟨17710870669467153679508485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23614494225956204906011313 17710870669467153679508485)
                  ·
                    refine ⟨3320788250525091314907841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17710870669467153679508485 3320788250525091314907841)
                    ·
                      refine ⟨2490591187893818486180881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3320788250525091314907841 2490591187893818486180881)
                      ·
                        rfl

theorem cell23_4850409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 4, 2].length) (baseStart_4850409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850409 prefixEnd_4850409 := by exact prefixLift 4850409
  have htrace : WordTrace (prefixWord ++ tailWord_4850409) baseStart_4850409 baseEnd_4850409 := by
    simpa [prefixWord, tailWord_4850409, baseEnd_4850409] using wordTrace_append hprefix tailTrace_4850409
  have hstable : (prefixWord ++ tailWord_4850409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850409).length < 2 ^ (prefixWord ++ tailWord_4850409).sum := by decide
  have hdescent : baseEnd_4850409 < baseStart_4850409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850429 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_4850429 : Nat := 118140960795 + 4850429 * 2 ^ 59
def prefixEnd_4850429 : Nat := 4983230072969 + 3 ^ 40 * 4850429 * 2
def baseEnd_4850429 : Nat := 2490601457506908407930789

theorem tailTrace_4850429 : CollatzResearch.WordTrace tailWord_4850429 prefixEnd_4850429 2490601457506908407930789 := by
  unfold tailWord_4850429
  simp only [CollatzResearch.WordTrace]
  refine ⟨176909679344731595167026341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117939786229821063444684227 176909679344731595167026341)
  ·
    refine ⟨33170564877137174093817439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176909679344731595167026341 33170564877137174093817439)
    ·
      refine ⟨49755847315705761140726159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33170564877137174093817439 49755847315705761140726159)
      ·
        refine ⟨74633770973558641711089239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49755847315705761140726159 74633770973558641711089239)
        ·
          refine ⟨111950656460337962566633859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74633770973558641711089239 111950656460337962566633859)
          ·
            refine ⟨167925984690506943849950789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111950656460337962566633859 167925984690506943849950789)
            ·
              refine ⟨31486122129470051971865773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167925984690506943849950789 31486122129470051971865773)
              ·
                refine ⟨11807295798551269489449665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31486122129470051971865773 11807295798551269489449665)
                ·
                  refine ⟨8855471848913452117087249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11807295798551269489449665 8855471848913452117087249)
                  ·
                    refine ⟨6641603886685089087815437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8855471848913452117087249 6641603886685089087815437)
                    ·
                      refine ⟨2490601457506908407930789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6641603886685089087815437 2490601457506908407930789)
                      ·
                        rfl

theorem cell23_4850429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_4850429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850429 prefixEnd_4850429 := by exact prefixLift 4850429
  have htrace : WordTrace (prefixWord ++ tailWord_4850429) baseStart_4850429 baseEnd_4850429 := by
    simpa [prefixWord, tailWord_4850429, baseEnd_4850429] using wordTrace_append hprefix tailTrace_4850429
  have hstable : (prefixWord ++ tailWord_4850429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850429).length < 2 ^ (prefixWord ++ tailWord_4850429).sum := by decide
  have hdescent : baseEnd_4850429 < baseStart_4850429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850453 : List Nat := [1, 3, 2, 1, 2, 2, 5, 2, 1, 4]
def baseStart_4850453 : Nat := 118140960795 + 4850453 * 2 ^ 59
def prefixEnd_4850453 : Nat := 4983230072969 + 3 ^ 40 * 4850453 * 2
def baseEnd_4850453 : Nat := 830204593680872104676893

theorem tailTrace_4850453 : CollatzResearch.WordTrace tailWord_4850453 prefixEnd_4850453 830204593680872104676893 := by
  unfold tailWord_4850453
  simp only [CollatzResearch.WordTrace]
  refine ⟨176910554696644647265900013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117940369797763098177266675 176910554696644647265900013)
  ·
    refine ⟨66341458011241742724712505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176910554696644647265900013 66341458011241742724712505)
    ·
      refine ⟨49756093508431307043534379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66341458011241742724712505 49756093508431307043534379)
      ·
        refine ⟨74634140262646960565301569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49756093508431307043534379 74634140262646960565301569)
        ·
          refine ⟨55975605196985220423976177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74634140262646960565301569 55975605196985220423976177)
          ·
            refine ⟨41981703897738915317982133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55975605196985220423976177 41981703897738915317982133)
            ·
              refine ⟨3935784740413023311060825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41981703897738915317982133 3935784740413023311060825)
              ·
                refine ⟨2951838555309767483295619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3935784740413023311060825 2951838555309767483295619)
                ·
                  refine ⟨4427757832964651224943429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2951838555309767483295619 4427757832964651224943429)
                  ·
                    refine ⟨830204593680872104676893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4427757832964651224943429 830204593680872104676893)
                    ·
                      rfl

theorem cell23_4850453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_4850453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850453 prefixEnd_4850453 := by exact prefixLift 4850453
  have htrace : WordTrace (prefixWord ++ tailWord_4850453) baseStart_4850453 baseEnd_4850453 := by
    simpa [prefixWord, tailWord_4850453, baseEnd_4850453] using wordTrace_append hprefix tailTrace_4850453
  have hstable : (prefixWord ++ tailWord_4850453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850453).length < 2 ^ (prefixWord ++ tailWord_4850453).sum := by decide
  have hdescent : baseEnd_4850453 < baseStart_4850453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850466 : List Nat := [3, 3, 1, 1, 2, 2, 4, 1, 6]
def baseStart_4850466 : Nat := 118140960795 + 4850466 * 2 ^ 59
def prefixEnd_4850466 : Nat := 4983230072969 + 3 ^ 40 * 4850466 * 2
def baseEnd_4850466 : Nat := 276735606254569418129791

theorem tailTrace_4850466 : CollatzResearch.WordTrace tailWord_4850466 prefixEnd_4850466 276735606254569418129791 := by
  unfold tailWord_4850466
  simp only [CollatzResearch.WordTrace]
  refine ⟨44227757211399387621530813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117940685897065033657415501 44227757211399387621530813)
  ·
    refine ⟨16585408954274770358074055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44227757211399387621530813 16585408954274770358074055)
    ·
      refine ⟨24878113431412155537111083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16585408954274770358074055 24878113431412155537111083)
      ·
        refine ⟨37317170147118233305666625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24878113431412155537111083 37317170147118233305666625)
        ·
          refine ⟨27987877610338674979249969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37317170147118233305666625 27987877610338674979249969)
          ·
            refine ⟨20990908207754006234437477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27987877610338674979249969 20990908207754006234437477)
            ·
              refine ⟨3935795288953876168957027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20990908207754006234437477 3935795288953876168957027)
              ·
                refine ⟨5903692933430814253435541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935795288953876168957027 5903692933430814253435541)
                ·
                  refine ⟨276735606254569418129791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5903692933430814253435541 276735606254569418129791)
                  ·
                    rfl

theorem cell23_4850466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_4850466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850466 prefixEnd_4850466 := by exact prefixLift 4850466
  have htrace : WordTrace (prefixWord ++ tailWord_4850466) baseStart_4850466 baseEnd_4850466 := by
    simpa [prefixWord, tailWord_4850466, baseEnd_4850466] using wordTrace_append hprefix tailTrace_4850466
  have hstable : (prefixWord ++ tailWord_4850466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850466).length < 2 ^ (prefixWord ++ tailWord_4850466).sum := by decide
  have hdescent : baseEnd_4850466 < baseStart_4850466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850512 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 6]
def baseStart_4850512 : Nat := 118140960795 + 4850512 * 2 ^ 59
def prefixEnd_4850512 : Nat := 4983230072969 + 3 ^ 40 * 4850512 * 2
def baseEnd_4850512 : Nat := 2490644076401231583192907

theorem tailTrace_4850512 : CollatzResearch.WordTrace tailWord_4850512 prefixEnd_4850512 2490644076401231583192907 := by
  unfold tailWord_4850512
  simp only [CollatzResearch.WordTrace]
  refine ⟨88456353301715450171148895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117941804402287266894865193 88456353301715450171148895)
  ·
    refine ⟨132684529952573175256723343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88456353301715450171148895 132684529952573175256723343)
    ·
      refine ⟨199026794928859762885085015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132684529952573175256723343 199026794928859762885085015)
      ·
        refine ⟨298540192393289644327627523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199026794928859762885085015 298540192393289644327627523)
        ·
          refine ⟨447810288589934466491441285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298540192393289644327627523 447810288589934466491441285)
          ·
            refine ⟨83964429110612712467145241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 447810288589934466491441285 83964429110612712467145241)
            ·
              refine ⟨62973321832959534350358931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83964429110612712467145241 62973321832959534350358931)
              ·
                refine ⟨94459982749439301525538397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62973321832959534350358931 94459982749439301525538397)
                ·
                  refine ⟨35422493531039738072076899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94459982749439301525538397 35422493531039738072076899)
                  ·
                    refine ⟨53133740296559607108115349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35422493531039738072076899 53133740296559607108115349)
                    ·
                      refine ⟨2490644076401231583192907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53133740296559607108115349 2490644076401231583192907)
                      ·
                        rfl

theorem cell23_4850512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_4850512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850512 prefixEnd_4850512 := by exact prefixLift 4850512
  have htrace : WordTrace (prefixWord ++ tailWord_4850512) baseStart_4850512 baseEnd_4850512 := by
    simpa [prefixWord, tailWord_4850512, baseEnd_4850512] using wordTrace_append hprefix tailTrace_4850512
  have hstable : (prefixWord ++ tailWord_4850512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850512).length < 2 ^ (prefixWord ++ tailWord_4850512).sum := by decide
  have hdescent : baseEnd_4850512 < baseStart_4850512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850536 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_4850536 : Nat := 118140960795 + 4850536 * 2 ^ 59
def prefixEnd_4850536 : Nat := 4983230072969 + 3 ^ 40 * 4850536 * 2
def baseEnd_4850536 : Nat := 2490656399936939489292797

theorem tailTrace_4850536 : CollatzResearch.WordTrace tailWord_4850536 prefixEnd_4850536 2490656399936939489292797 := by
  unfold tailWord_4850536
  simp only [CollatzResearch.WordTrace]
  refine ⟨88456790977671976220585731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117942387970229301627447641 88456790977671976220585731)
  ·
    refine ⟨132685186466507964330878597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88456790977671976220585731 132685186466507964330878597)
    ·
      refine ⟨24878472462470243312039737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132685186466507964330878597 24878472462470243312039737)
      ·
        refine ⟨18658854346852682484029803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24878472462470243312039737 18658854346852682484029803)
        ·
          refine ⟨27988281520279023726044705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18658854346852682484029803 27988281520279023726044705)
          ·
            refine ⟨20991211140209267794533529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27988281520279023726044705 20991211140209267794533529)
            ·
              refine ⟨15743408355156950845900147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20991211140209267794533529 15743408355156950845900147)
              ·
                refine ⟨23615112532735426268850221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15743408355156950845900147 23615112532735426268850221)
                ·
                  refine ⟨8855667199775784850818833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23615112532735426268850221 8855667199775784850818833)
                  ·
                    refine ⟨6641750399831838638114125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8855667199775784850818833 6641750399831838638114125)
                    ·
                      refine ⟨2490656399936939489292797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6641750399831838638114125 2490656399936939489292797)
                      ·
                        rfl

theorem cell23_4850536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_4850536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850536 prefixEnd_4850536 := by exact prefixLift 4850536
  have htrace : WordTrace (prefixWord ++ tailWord_4850536) baseStart_4850536 baseEnd_4850536 := by
    simpa [prefixWord, tailWord_4850536, baseEnd_4850536] using wordTrace_append hprefix tailTrace_4850536
  have hstable : (prefixWord ++ tailWord_4850536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850536).length < 2 ^ (prefixWord ++ tailWord_4850536).sum := by decide
  have hdescent : baseEnd_4850536 < baseStart_4850536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850550 : List Nat := [5, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_4850550 : Nat := 118140960795 + 4850550 * 2 ^ 59
def prefixEnd_4850550 : Nat := 4983230072969 + 3 ^ 40 * 4850550 * 2
def baseEnd_4850550 : Nat := 2490663588666102434517733

theorem tailTrace_4850550 : CollatzResearch.WordTrace tailWord_4850550 prefixEnd_4850550 2490663588666102434517733 := by
  unfold tailWord_4850550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11057130786080827052011319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117942728384862155221454069 11057130786080827052011319)
  ·
    refine ⟨16585696179121240578016979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11057130786080827052011319 16585696179121240578016979)
    ·
      refine ⟨24878544268681860867025469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16585696179121240578016979 24878544268681860867025469)
      ·
        refine ⟨9329454100755697825134551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24878544268681860867025469 9329454100755697825134551)
        ·
          refine ⟨13994181151133546737701827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9329454100755697825134551 13994181151133546737701827)
          ·
            refine ⟨20991271726700320106552741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13994181151133546737701827 20991271726700320106552741)
            ·
              refine ⟨3935863448756310019978639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20991271726700320106552741 3935863448756310019978639)
              ·
                refine ⟨5903795173134465029967959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935863448756310019978639 5903795173134465029967959)
                ·
                  refine ⟨8855692759701697544951939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5903795173134465029967959 8855692759701697544951939)
                  ·
                    refine ⟨13283539139552546317427909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8855692759701697544951939 13283539139552546317427909)
                    ·
                      refine ⟨2490663588666102434517733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13283539139552546317427909 2490663588666102434517733)
                      ·
                        rfl

theorem cell23_4850550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_4850550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850550 prefixEnd_4850550 := by exact prefixLift 4850550
  have htrace : WordTrace (prefixWord ++ tailWord_4850550) baseStart_4850550 baseEnd_4850550 := by
    simpa [prefixWord, tailWord_4850550, baseEnd_4850550] using wordTrace_append hprefix tailTrace_4850550
  have hstable : (prefixWord ++ tailWord_4850550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850550).length < 2 ^ (prefixWord ++ tailWord_4850550).sum := by decide
  have hdescent : baseEnd_4850550 < baseStart_4850550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850552 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 1, 9]
def baseStart_4850552 : Nat := 118140960795 + 4850552 * 2 ^ 59
def prefixEnd_4850552 : Nat := 4983230072969 + 3 ^ 40 * 4850552 * 2
def baseEnd_4850552 : Nat := 830221538542470475564241

theorem tailTrace_4850552 : CollatzResearch.WordTrace tailWord_4850552 prefixEnd_4850552 830221538542470475564241 := by
  unfold tailWord_4850552
  simp only [CollatzResearch.WordTrace]
  refine ⟨88457082761642993586876955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117942777015523991449169273 88457082761642993586876955)
  ·
    refine ⟨132685624142464490380315433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88457082761642993586876955 132685624142464490380315433)
    ·
      refine ⟨99514218106848367785236575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132685624142464490380315433 99514218106848367785236575)
      ·
        refine ⟨149271327160272551677854863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99514218106848367785236575 149271327160272551677854863)
        ·
          refine ⟨223906990740408827516782295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149271327160272551677854863 223906990740408827516782295)
          ·
            refine ⟨335860486110613241275173443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223906990740408827516782295 335860486110613241275173443)
            ·
              refine ⟨503790729165919861912760165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335860486110613241275173443 503790729165919861912760165)
              ·
                refine ⟨94460761718609974108642531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 503790729165919861912760165 94460761718609974108642531)
                ·
                  refine ⟨141691142577914961162963797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94460761718609974108642531 141691142577914961162963797)
                  ·
                    refine ⟨830221538542470475564241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 141691142577914961162963797 830221538542470475564241)
                    ·
                      rfl

theorem cell23_4850552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_4850552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850552 prefixEnd_4850552 := by exact prefixLift 4850552
  have htrace : WordTrace (prefixWord ++ tailWord_4850552) baseStart_4850552 baseEnd_4850552 := by
    simpa [prefixWord, tailWord_4850552, baseEnd_4850552] using wordTrace_append hprefix tailTrace_4850552
  have hstable : (prefixWord ++ tailWord_4850552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850552).length < 2 ^ (prefixWord ++ tailWord_4850552).sum := by decide
  have hdescent : baseEnd_4850552 < baseStart_4850552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850553 : List Nat := [1, 2, 1, 3, 2, 3, 4, 1, 1, 2, 3]
def baseStart_4850553 : Nat := 118140960795 + 4850553 * 2 ^ 59
def prefixEnd_4850553 : Nat := 4983230072969 + 3 ^ 40 * 4850553 * 2
def baseEnd_4850553 : Nat := 2490665129108065922780219

theorem tailTrace_4850553 : CollatzResearch.WordTrace tailWord_4850553 prefixEnd_4850553 2490665129108065922780219 := by
  unfold tailWord_4850553
  simp only [CollatzResearch.WordTrace]
  refine ⟨176914201996282364344540313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117942801330854909563026875 176914201996282364344540313)
  ·
    refine ⟨132685651497211773258405235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176914201996282364344540313 132685651497211773258405235)
    ·
      refine ⟨199028477245817659887607853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132685651497211773258405235 199028477245817659887607853)
      ·
        refine ⟨74635678967181622457852945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199028477245817659887607853 74635678967181622457852945)
        ·
          refine ⟨55976759225386216843389709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74635678967181622457852945 55976759225386216843389709)
          ·
            refine ⟨20991284709519831316271141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55976759225386216843389709 20991284709519831316271141)
            ·
              refine ⟨3935865883034968371800839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20991284709519831316271141 3935865883034968371800839)
              ·
                refine ⟨5903798824552452557701259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3935865883034968371800839 5903798824552452557701259)
                ·
                  refine ⟨8855698236828678836551889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5903798824552452557701259 8855698236828678836551889)
                  ·
                    refine ⟨6641773677621509127413917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8855698236828678836551889 6641773677621509127413917)
                    ·
                      refine ⟨2490665129108065922780219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6641773677621509127413917 2490665129108065922780219)
                      ·
                        rfl

theorem cell23_4850553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_4850553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850553 prefixEnd_4850553 := by exact prefixLift 4850553
  have htrace : WordTrace (prefixWord ++ tailWord_4850553) baseStart_4850553 baseEnd_4850553 := by
    simpa [prefixWord, tailWord_4850553, baseEnd_4850553] using wordTrace_append hprefix tailTrace_4850553
  have hstable : (prefixWord ++ tailWord_4850553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850553).length < 2 ^ (prefixWord ++ tailWord_4850553).sum := by decide
  have hdescent : baseEnd_4850553 < baseStart_4850553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850674 : List Nat := [3, 2, 1, 5, 1, 1, 2, 2, 2, 2, 2]
def baseStart_4850674 : Nat := 118140960795 + 4850674 * 2 ^ 59
def prefixEnd_4850674 : Nat := 4983230072969 + 3 ^ 40 * 4850674 * 2
def baseEnd_4850674 : Nat := 2490727260267259949367163

theorem tailTrace_4850674 : CollatzResearch.WordTrace tailWord_4850674 prefixEnd_4850674 2490727260267259949367163 := by
  unfold tailWord_4850674
  simp only [CollatzResearch.WordTrace]
  refine ⟨44229653807211000502423769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117945743485896001339796717 44229653807211000502423769)
  ·
    refine ⟨33172240355408250376817827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44229653807211000502423769 33172240355408250376817827)
    ·
      refine ⟨49758360533112375565226741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33172240355408250376817827 49758360533112375565226741)
      ·
        refine ⟨4664846299979285209240007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49758360533112375565226741 4664846299979285209240007)
        ·
          refine ⟨6997269449968927813860011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664846299979285209240007 6997269449968927813860011)
          ·
            refine ⟨10495904174953391720790017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6997269449968927813860011 10495904174953391720790017)
            ·
              refine ⟨7871928131215043790592513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10495904174953391720790017 7871928131215043790592513)
              ·
                refine ⟨5903946098411282842944385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7871928131215043790592513 5903946098411282842944385)
                ·
                  refine ⟨4427959573808462132208289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5903946098411282842944385 4427959573808462132208289)
                  ·
                    refine ⟨3320969680356346599156217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4427959573808462132208289 3320969680356346599156217)
                    ·
                      refine ⟨2490727260267259949367163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3320969680356346599156217 2490727260267259949367163)
                      ·
                        rfl

theorem cell23_4850674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_4850674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850674 prefixEnd_4850674 := by exact prefixLift 4850674
  have htrace : WordTrace (prefixWord ++ tailWord_4850674) baseStart_4850674 baseEnd_4850674 := by
    simpa [prefixWord, tailWord_4850674, baseEnd_4850674] using wordTrace_append hprefix tailTrace_4850674
  have hstable : (prefixWord ++ tailWord_4850674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850674).length < 2 ^ (prefixWord ++ tailWord_4850674).sum := by decide
  have hdescent : baseEnd_4850674 < baseStart_4850674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850740 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_4850740 : Nat := 118140960795 + 4850740 * 2 ^ 59
def prefixEnd_4850740 : Nat := 4983230072969 + 3 ^ 40 * 4850740 * 2
def baseEnd_4850740 : Nat := 830253716663485563713953

theorem tailTrace_4850740 : CollatzResearch.WordTrace tailWord_4850740 prefixEnd_4850740 830253716663485563713953 := by
  unfold tailWord_4850740
  simp only [CollatzResearch.WordTrace]
  refine ⟨88460511223302447640798837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117947348297736596854398449 88460511223302447640798837)
  ·
    refine ⟨8293172927184604466324891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88460511223302447640798837 8293172927184604466324891)
    ·
      refine ⟨12439759390776906699487337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8293172927184604466324891 12439759390776906699487337)
      ·
        refine ⟨9329819543082680024615503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12439759390776906699487337 9329819543082680024615503)
        ·
          refine ⟨13994729314624020036923255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9329819543082680024615503 13994729314624020036923255)
          ·
            refine ⟨20992093971936030055384883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13994729314624020036923255 20992093971936030055384883)
            ·
              refine ⟨31488140957904045083077325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20992093971936030055384883 31488140957904045083077325)
              ·
                refine ⟨11808052859214016906153997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31488140957904045083077325 11808052859214016906153997)
                ·
                  refine ⟨4428019822205256339807749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11808052859214016906153997 4428019822205256339807749)
                  ·
                    refine ⟨830253716663485563713953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4428019822205256339807749 830253716663485563713953)
                    ·
                      rfl

theorem cell23_4850740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_4850740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850740 prefixEnd_4850740 := by exact prefixLift 4850740
  have htrace : WordTrace (prefixWord ++ tailWord_4850740) baseStart_4850740 baseEnd_4850740 := by
    simpa [prefixWord, tailWord_4850740, baseEnd_4850740] using wordTrace_append hprefix tailTrace_4850740
  have hstable : (prefixWord ++ tailWord_4850740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850740).length < 2 ^ (prefixWord ++ tailWord_4850740).sum := by decide
  have hdescent : baseEnd_4850740 < baseStart_4850740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850773 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 1, 5, 2]
def baseStart_4850773 : Nat := 118140960795 + 4850773 * 2 ^ 59
def prefixEnd_4850773 : Nat := 4983230072969 + 3 ^ 40 * 4850773 * 2
def baseEnd_4850773 : Nat := 2490778094852055062029207

theorem tailTrace_4850773 : CollatzResearch.WordTrace tailWord_4850773 prefixEnd_4850773 2490778094852055062029207 := by
  unfold tailWord_4850773
  simp only [CollatzResearch.WordTrace]
  refine ⟨176922226055485341917548973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117948150703656894611699315 176922226055485341917548973)
  ·
    refine ⟨66345834770807003219080865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176922226055485341917548973 66345834770807003219080865)
    ·
      refine ⟨49759376078105252414310649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66345834770807003219080865 49759376078105252414310649)
      ·
        refine ⟨37319532058578939310732987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49759376078105252414310649 37319532058578939310732987)
        ·
          refine ⟨55979298087868408966099481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37319532058578939310732987 55979298087868408966099481)
          ·
            refine ⟨41984473565901306724574611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55979298087868408966099481 41984473565901306724574611)
            ·
              refine ⟨62976710348851960086861917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41984473565901306724574611 62976710348851960086861917)
              ·
                refine ⟨23616266380819485032573219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62976710348851960086861917 23616266380819485032573219)
                ·
                  refine ⟨35424399571229227548859829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23616266380819485032573219 35424399571229227548859829)
                  ·
                    refine ⟨3321037459802740082705609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35424399571229227548859829 3321037459802740082705609)
                    ·
                      refine ⟨2490778094852055062029207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321037459802740082705609 2490778094852055062029207)
                      ·
                        rfl

theorem cell23_4850773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_4850773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850773 prefixEnd_4850773 := by exact prefixLift 4850773
  have htrace : WordTrace (prefixWord ++ tailWord_4850773) baseStart_4850773 baseEnd_4850773 := by
    simpa [prefixWord, tailWord_4850773, baseEnd_4850773] using wordTrace_append hprefix tailTrace_4850773
  have hstable : (prefixWord ++ tailWord_4850773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850773).length < 2 ^ (prefixWord ++ tailWord_4850773).sum := by decide
  have hdescent : baseEnd_4850773 < baseStart_4850773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850797 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_4850797 : Nat := 118140960795 + 4850797 * 2 ^ 59
def prefixEnd_4850797 : Nat := 4983230072969 + 3 ^ 40 * 4850797 * 2
def baseEnd_4850797 : Nat := 2490790418387762968129097

theorem tailTrace_4850797 : CollatzResearch.WordTrace tailWord_4850797 prefixEnd_4850797 2490790418387762968129097 := by
  unfold tailWord_4850797
  simp only [CollatzResearch.WordTrace]
  refine ⟨176923101407398394016422645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117948734271598929344281763 176923101407398394016422645)
  ·
    refine ⟨16586540756943599439039623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176923101407398394016422645 16586540756943599439039623)
    ·
      refine ⟨24879811135415399158559435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16586540756943599439039623 24879811135415399158559435)
      ·
        refine ⟨37319716703123098737839153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24879811135415399158559435 37319716703123098737839153)
        ·
          refine ⟨27989787527342324053379365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37319716703123098737839153 27989787527342324053379365)
          ·
            refine ⟨5248085161376685760008631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27989787527342324053379365 5248085161376685760008631)
            ·
              refine ⟨7872127742065028640012947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5248085161376685760008631 7872127742065028640012947)
              ·
                refine ⟨11808191613097542960019421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7872127742065028640012947 11808191613097542960019421)
                ·
                  refine ⟨4428071854911578610007283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11808191613097542960019421 4428071854911578610007283)
                  ·
                    refine ⟨6642107782367367915010925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4428071854911578610007283 6642107782367367915010925)
                    ·
                      refine ⟨2490790418387762968129097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6642107782367367915010925 2490790418387762968129097)
                      ·
                        rfl

theorem cell23_4850797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_4850797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850797 prefixEnd_4850797 := by exact prefixLift 4850797
  have htrace : WordTrace (prefixWord ++ tailWord_4850797) baseStart_4850797 baseEnd_4850797 := by
    simpa [prefixWord, tailWord_4850797, baseEnd_4850797] using wordTrace_append hprefix tailTrace_4850797
  have hstable : (prefixWord ++ tailWord_4850797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850797).length < 2 ^ (prefixWord ++ tailWord_4850797).sum := by decide
  have hdescent : baseEnd_4850797 < baseStart_4850797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850816 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 6]
def baseStart_4850816 : Nat := 118140960795 + 4850816 * 2 ^ 59
def prefixEnd_4850816 : Nat := 4983230072969 + 3 ^ 40 * 4850816 * 2
def baseEnd_4850816 : Nat := 2490800174520198393791509

theorem tailTrace_4850816 : CollatzResearch.WordTrace tailWord_4850816 prefixEnd_4850816 2490800174520198393791509 := by
  unfold tailWord_4850816
  simp only [CollatzResearch.WordTrace]
  refine ⟨88461897197164780130682151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117949196262886373507576201 88461897197164780130682151)
  ·
    refine ⟨132692845795747170196023227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88461897197164780130682151 132692845795747170196023227)
    ·
      refine ⟨199039268693620755294034841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132692845795747170196023227 199039268693620755294034841)
      ·
        refine ⟨149279451520215566470526131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199039268693620755294034841 149279451520215566470526131)
        ·
          refine ⟨223919177280323349705789197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149279451520215566470526131 223919177280323349705789197)
          ·
            refine ⟨83969691480121256139670949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223919177280323349705789197 83969691480121256139670949)
            ·
              refine ⟨15744317152522735526188303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83969691480121256139670949 15744317152522735526188303)
              ·
                refine ⟨23616475728784103289282455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15744317152522735526188303 23616475728784103289282455)
                ·
                  refine ⟨35424713593176154933923683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23616475728784103289282455 35424713593176154933923683)
                  ·
                    refine ⟨53137070389764232400885525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35424713593176154933923683 53137070389764232400885525)
                    ·
                      refine ⟨2490800174520198393791509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53137070389764232400885525 2490800174520198393791509)
                      ·
                        rfl

theorem cell23_4850816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_4850816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850816 prefixEnd_4850816 := by exact prefixLift 4850816
  have htrace : WordTrace (prefixWord ++ tailWord_4850816) baseStart_4850816 baseEnd_4850816 := by
    simpa [prefixWord, tailWord_4850816, baseEnd_4850816] using wordTrace_append hprefix tailTrace_4850816
  have hstable : (prefixWord ++ tailWord_4850816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850816).length < 2 ^ (prefixWord ++ tailWord_4850816).sum := by decide
  have hdescent : baseEnd_4850816 < baseStart_4850816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850820 : List Nat := [2, 3, 2, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_4850820 : Nat := 118140960795 + 4850820 * 2 ^ 59
def prefixEnd_4850820 : Nat := 4983230072969 + 3 ^ 40 * 4850820 * 2
def baseEnd_4850820 : Nat := 2490802228442816378141491

theorem tailTrace_4850820 : CollatzResearch.WordTrace tailWord_4850820 prefixEnd_4850820 2490802228442816378141491 := by
  unfold tailWord_4850820
  simp only [CollatzResearch.WordTrace]
  refine ⟨88461970143157534472254957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117949293524210045963006609 88461970143157534472254957)
  ·
    refine ⟨33173238803684075427095609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88461970143157534472254957 33173238803684075427095609)
    ·
      refine ⟨24879929102763056570321707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33173238803684075427095609 24879929102763056570321707)
      ·
        refine ⟨37319893654144584855482561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24879929102763056570321707 37319893654144584855482561)
        ·
          refine ⟨27989920240608438641611921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37319893654144584855482561 27989920240608438641611921)
          ·
            refine ⟨20992440180456328981208941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27989920240608438641611921 20992440180456328981208941)
            ·
              refine ⟨7872165067671123367953353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20992440180456328981208941 7872165067671123367953353)
              ·
                refine ⟨5904123800753342525965015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7872165067671123367953353 5904123800753342525965015)
                ·
                  refine ⟨8856185701130013788947523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5904123800753342525965015 8856185701130013788947523)
                  ·
                    refine ⟨13284278551695020683421285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8856185701130013788947523 13284278551695020683421285)
                    ·
                      refine ⟨2490802228442816378141491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13284278551695020683421285 2490802228442816378141491)
                      ·
                        rfl

theorem cell23_4850820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_4850820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850820 prefixEnd_4850820 := by exact prefixLift 4850820
  have htrace : WordTrace (prefixWord ++ tailWord_4850820) baseStart_4850820 baseEnd_4850820 := by
    simpa [prefixWord, tailWord_4850820, baseEnd_4850820] using wordTrace_append hprefix tailTrace_4850820
  have hstable : (prefixWord ++ tailWord_4850820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850820).length < 2 ^ (prefixWord ++ tailWord_4850820).sum := by decide
  have hdescent : baseEnd_4850820 < baseStart_4850820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850826 : List Nat := [3, 1, 2, 3, 1, 1, 1, 11]
def baseStart_4850826 : Nat := 118140960795 + 4850826 * 2 ^ 59
def prefixEnd_4850826 : Nat := 4983230072969 + 3 ^ 40 * 4850826 * 2
def baseEnd_4850826 : Nat := 92252048493583087209869

theorem tailTrace_4850826 : CollatzResearch.WordTrace tailWord_4850826 prefixEnd_4850826 92252048493583087209869 := by
  unfold tailWord_4850826
  simp only [CollatzResearch.WordTrace]
  refine ⟨44231039781073332992307083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117949439416195554646152221 44231039781073332992307083)
  ·
    refine ⟨66346559671609999488460625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44231039781073332992307083 66346559671609999488460625)
    ·
      refine ⟨49759919753707499616345469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66346559671609999488460625 49759919753707499616345469)
      ·
        refine ⟨18659969907640312356129551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49759919753707499616345469 18659969907640312356129551)
        ·
          refine ⟨27989954861460468534194327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18659969907640312356129551 27989954861460468534194327)
          ·
            refine ⟨41984932292190702801291491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27989954861460468534194327 41984932292190702801291491)
            ·
              refine ⟨62977398438286054201937237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41984932292190702801291491 62977398438286054201937237)
              ·
                refine ⟨92252048493583087209869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 62977398438286054201937237 92252048493583087209869)
                ·
                  rfl

theorem cell23_4850826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 11].length) (baseStart_4850826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850826 prefixEnd_4850826 := by exact prefixLift 4850826
  have htrace : WordTrace (prefixWord ++ tailWord_4850826) baseStart_4850826 baseEnd_4850826 := by
    simpa [prefixWord, tailWord_4850826, baseEnd_4850826] using wordTrace_append hprefix tailTrace_4850826
  have hstable : (prefixWord ++ tailWord_4850826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850826).length < 2 ^ (prefixWord ++ tailWord_4850826).sum := by decide
  have hdescent : baseEnd_4850826 < baseStart_4850826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850840 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 1, 1, 5]
def baseStart_4850840 : Nat := 118140960795 + 4850840 * 2 ^ 59
def prefixEnd_4850840 : Nat := 4983230072969 + 3 ^ 40 * 4850840 * 2
def baseEnd_4850840 : Nat := 2490812498055906299891399

theorem tailTrace_4850840 : CollatzResearch.WordTrace tailWord_4850840 prefixEnd_4850840 2490812498055906299891399 := by
  unfold tailWord_4850840
  simp only [CollatzResearch.WordTrace]
  refine ⟨88462334873121306180118987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117949779830828408240158649 88462334873121306180118987)
  ·
    refine ⟨132693502309681959270178481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88462334873121306180118987 132693502309681959270178481)
    ·
      refine ⟨99520126732261469452633861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132693502309681959270178481 99520126732261469452633861)
      ·
        refine ⟨18660023762299025522368849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99520126732261469452633861 18660023762299025522368849)
        ·
          refine ⟨13995017821724269141776637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18660023762299025522368849 13995017821724269141776637)
          ·
            refine ⟨5248131683146600928166239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13995017821724269141776637 5248131683146600928166239)
            ·
              refine ⟨7872197524719901392249359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5248131683146600928166239 7872197524719901392249359)
              ·
                refine ⟨11808296287079852088374039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7872197524719901392249359 11808296287079852088374039)
                ·
                  refine ⟨17712444430619778132561059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11808296287079852088374039 17712444430619778132561059)
                  ·
                    refine ⟨26568666645929667198841589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17712444430619778132561059 26568666645929667198841589)
                    ·
                      refine ⟨2490812498055906299891399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26568666645929667198841589 2490812498055906299891399)
                      ·
                        rfl

theorem cell23_4850840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_4850840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850840 prefixEnd_4850840 := by exact prefixLift 4850840
  have htrace : WordTrace (prefixWord ++ tailWord_4850840) baseStart_4850840 baseEnd_4850840 := by
    simpa [prefixWord, tailWord_4850840, baseEnd_4850840] using wordTrace_append hprefix tailTrace_4850840
  have hstable : (prefixWord ++ tailWord_4850840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850840).length < 2 ^ (prefixWord ++ tailWord_4850840).sum := by decide
  have hdescent : baseEnd_4850840 < baseStart_4850840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850847 : List Nat := [1, 1, 2, 6, 2, 1, 2, 2, 2, 4]
def baseStart_4850847 : Nat := 118140960795 + 4850847 * 2 ^ 59
def prefixEnd_4850847 : Nat := 4983230072969 + 3 ^ 40 * 4850847 * 2
def baseEnd_4850847 : Nat := 830272030806829257501289

theorem tailTrace_4850847 : CollatzResearch.WordTrace tailWord_4850847 prefixEnd_4850847 830272030806829257501289 := by
  unfold tailWord_4850847
  simp only [CollatzResearch.WordTrace]
  refine ⟨176924925057217252555742795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117949950038144835037161863 176924925057217252555742795)
  ·
    refine ⟨265387387585825878833614193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176924925057217252555742795 265387387585825878833614193)
    ·
      refine ⟨199040540689369409125210645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265387387585825878833614193 199040540689369409125210645)
      ·
        refine ⟨9330025344814191052744249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 199040540689369409125210645 9330025344814191052744249)
        ·
          refine ⟨6997519008610643289558187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9330025344814191052744249 6997519008610643289558187)
          ·
            refine ⟨10496278512915964934337281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6997519008610643289558187 10496278512915964934337281)
            ·
              refine ⟨7872208884686973700752961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10496278512915964934337281 7872208884686973700752961)
              ·
                refine ⟨5904156663515230275564721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7872208884686973700752961 5904156663515230275564721)
                ·
                  refine ⟨4428117497636422706673541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5904156663515230275564721 4428117497636422706673541)
                  ·
                    refine ⟨830272030806829257501289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4428117497636422706673541 830272030806829257501289)
                    ·
                      rfl

theorem cell23_4850847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 4].length) (baseStart_4850847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850847 prefixEnd_4850847 := by exact prefixLift 4850847
  have htrace : WordTrace (prefixWord ++ tailWord_4850847) baseStart_4850847 baseEnd_4850847 := by
    simpa [prefixWord, tailWord_4850847, baseEnd_4850847] using wordTrace_append hprefix tailTrace_4850847
  have hstable : (prefixWord ++ tailWord_4850847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850847).length < 2 ^ (prefixWord ++ tailWord_4850847).sum := by decide
  have hdescent : baseEnd_4850847 < baseStart_4850847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850904 : List Nat := [2, 1, 2, 2, 5, 2, 1, 2, 2, 1, 3]
def baseStart_4850904 : Nat := 118140960795 + 4850904 * 2 ^ 59
def prefixEnd_4850904 : Nat := 4983230072969 + 3 ^ 40 * 4850904 * 2
def baseEnd_4850904 : Nat := 2490845360817794049491105

theorem tailTrace_4850904 : CollatzResearch.WordTrace tailWord_4850904 prefixEnd_4850904 2490845360817794049491105 := by
  unfold tailWord_4850904
  simp only [CollatzResearch.WordTrace]
  refine ⟨88463502009005375645283883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117951336012007167527045177 88463502009005375645283883)
  ·
    refine ⟨132695253013508063467925825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88463502009005375645283883 132695253013508063467925825)
    ·
      refine ⟨99521439760131047600944369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132695253013508063467925825 99521439760131047600944369)
      ·
        refine ⟨74641079820098285700708277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99521439760131047600944369 74641079820098285700708277)
        ·
          refine ⟨6997601233134214284441401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74641079820098285700708277 6997601233134214284441401)
          ·
            refine ⟨5248200924850660713331051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6997601233134214284441401 5248200924850660713331051)
            ·
              refine ⟨7872301387275991069996577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5248200924850660713331051 7872301387275991069996577)
              ·
                refine ⟨5904226040456993302497433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7872301387275991069996577 5904226040456993302497433)
                ·
                  refine ⟨4428169530342744976873075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5904226040456993302497433 4428169530342744976873075)
                  ·
                    refine ⟨6642254295514117465309613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4428169530342744976873075 6642254295514117465309613)
                    ·
                      refine ⟨2490845360817794049491105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6642254295514117465309613 2490845360817794049491105)
                      ·
                        rfl

theorem cell23_4850904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_4850904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850904 prefixEnd_4850904 := by exact prefixLift 4850904
  have htrace : WordTrace (prefixWord ++ tailWord_4850904) baseStart_4850904 baseEnd_4850904 := by
    simpa [prefixWord, tailWord_4850904, baseEnd_4850904] using wordTrace_append hprefix tailTrace_4850904
  have hstable : (prefixWord ++ tailWord_4850904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850904).length < 2 ^ (prefixWord ++ tailWord_4850904).sum := by decide
  have hdescent : baseEnd_4850904 < baseStart_4850904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850923 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 4]
def baseStart_4850923 : Nat := 118140960795 + 4850923 * 2 ^ 59
def prefixEnd_4850923 : Nat := 4983230072969 + 3 ^ 40 * 4850923 * 2
def baseEnd_4850923 : Nat := 2490855116950229475153517

theorem tailTrace_4850923 : CollatzResearch.WordTrace tailWord_4850923 prefixEnd_4850923 2490855116950229475153517 := by
  unfold tailWord_4850923
  simp only [CollatzResearch.WordTrace]
  refine ⟨176927697004941917535509423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117951798003294611690339615 176927697004941917535509423)
  ·
    refine ⟨265391545507412876303264135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176927697004941917535509423 265391545507412876303264135)
    ·
      refine ⟨398087318261119314454896203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265391545507412876303264135 398087318261119314454896203)
      ·
        refine ⟨597130977391678971682344305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398087318261119314454896203 597130977391678971682344305)
        ·
          refine ⟨447848233043759228761758229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597130977391678971682344305 447848233043759228761758229)
          ·
            refine ⟨20992885923926213848207417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 447848233043759228761758229 20992885923926213848207417)
            ·
              refine ⟨15744664442944660386155563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20992885923926213848207417 15744664442944660386155563)
              ·
                refine ⟨23616996664416990579233345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15744664442944660386155563 23616996664416990579233345)
                ·
                  refine ⟨17712747498312742934425009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23616996664416990579233345 17712747498312742934425009)
                  ·
                    refine ⟨13284560623734557200818757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17712747498312742934425009 13284560623734557200818757)
                    ·
                      refine ⟨2490855116950229475153517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13284560623734557200818757 2490855116950229475153517)
                      ·
                        rfl

theorem cell23_4850923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 4].length) (baseStart_4850923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850923 prefixEnd_4850923 := by exact prefixLift 4850923
  have htrace : WordTrace (prefixWord ++ tailWord_4850923) baseStart_4850923 baseEnd_4850923 := by
    simpa [prefixWord, tailWord_4850923, baseEnd_4850923] using wordTrace_append hprefix tailTrace_4850923
  have hstable : (prefixWord ++ tailWord_4850923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850923).length < 2 ^ (prefixWord ++ tailWord_4850923).sum := by decide
  have hdescent : baseEnd_4850923 < baseStart_4850923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850967 : List Nat := [1, 1, 3, 4, 1, 1, 5, 2, 5]
def baseStart_4850967 : Nat := 118140960795 + 4850967 * 2 ^ 59
def prefixEnd_4850967 : Nat := 4983230072969 + 3 ^ 40 * 4850967 * 2
def baseEnd_4850967 : Nat := 276764190011003033667035

theorem tailTrace_4850967 : CollatzResearch.WordTrace tailWord_4850967 prefixEnd_4850967 276764190011003033667035 := by
  unfold tailWord_4850967
  simp only [CollatzResearch.WordTrace]
  refine ⟨176929301816782513050111155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117952867877855008700074103 176929301816782513050111155)
  ·
    refine ⟨265393952725173769575166733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176929301816782513050111155 265393952725173769575166733)
    ·
      refine ⟨99522732271940163590687525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265393952725173769575166733 99522732271940163590687525)
      ·
        refine ⟨18660512300988780673253911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99522732271940163590687525 18660512300988780673253911)
        ·
          refine ⟨27990768451483171009880867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18660512300988780673253911 27990768451483171009880867)
          ·
            refine ⟨41986152677224756514821301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27990768451483171009880867 41986152677224756514821301)
            ·
              refine ⟨3936201813489820923264497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41986152677224756514821301 3936201813489820923264497)
              ·
                refine ⟨2952151360117365692448373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3936201813489820923264497 2952151360117365692448373)
                ·
                  refine ⟨276764190011003033667035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2952151360117365692448373 276764190011003033667035)
                  ·
                    rfl

theorem cell23_4850967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 2, 5].length) (baseStart_4850967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850967 prefixEnd_4850967 := by exact prefixLift 4850967
  have htrace : WordTrace (prefixWord ++ tailWord_4850967) baseStart_4850967 baseEnd_4850967 := by
    simpa [prefixWord, tailWord_4850967, baseEnd_4850967] using wordTrace_append hprefix tailTrace_4850967
  have hstable : (prefixWord ++ tailWord_4850967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850967).length < 2 ^ (prefixWord ++ tailWord_4850967).sum := by decide
  have hdescent : baseEnd_4850967 < baseStart_4850967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4850978 : List Nat := [3, 3, 1, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_4850978 : Nat := 118140960795 + 4850978 * 2 ^ 59
def prefixEnd_4850978 : Nat := 4983230072969 + 3 ^ 40 * 4850978 * 2
def baseEnd_4850978 : Nat := 2490883358386226759965765

theorem tailTrace_4850978 : CollatzResearch.WordTrace tailWord_4850978 prefixEnd_4850978 2490883358386226759965765 := by
  unfold tailWord_4850978
  simp only [CollatzResearch.WordTrace]
  refine ⟨44232425754935665482190397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117953135346495107952507725 44232425754935665482190397)
  ·
    refine ⟨16587159658100874555821399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44232425754935665482190397 16587159658100874555821399)
    ·
      refine ⟨24880739487151311833732099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16587159658100874555821399 24880739487151311833732099)
      ·
        refine ⟨37321109230726967750598149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24880739487151311833732099 37321109230726967750598149)
        ·
          refine ⟨6997707980761306453237153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37321109230726967750598149 6997707980761306453237153)
          ·
            refine ⟨5248280985570979839927865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6997707980761306453237153 5248280985570979839927865)
            ·
              refine ⟨3936210739178234879945899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5248280985570979839927865 3936210739178234879945899)
              ·
                refine ⟨5904316108767352319918849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3936210739178234879945899 5904316108767352319918849)
                ·
                  refine ⟨4428237081575514239939137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5904316108767352319918849 4428237081575514239939137)
                  ·
                    refine ⟨3321177811181635679954353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4428237081575514239939137 3321177811181635679954353)
                    ·
                      refine ⟨2490883358386226759965765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321177811181635679954353 2490883358386226759965765)
                      ·
                        rfl

theorem cell23_4850978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_4850978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4850978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4850978 prefixEnd_4850978 := by exact prefixLift 4850978
  have htrace : WordTrace (prefixWord ++ tailWord_4850978) baseStart_4850978 baseEnd_4850978 := by
    simpa [prefixWord, tailWord_4850978, baseEnd_4850978] using wordTrace_append hprefix tailTrace_4850978
  have hstable : (prefixWord ++ tailWord_4850978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4850978).length < 2 ^ (prefixWord ++ tailWord_4850978).sum := by decide
  have hdescent : baseEnd_4850978 < baseStart_4850978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4850978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851000 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 4, 4, 2]
def baseStart_4851000 : Nat := 118140960795 + 4851000 * 2 ^ 59
def prefixEnd_4851000 : Nat := 4983230072969 + 3 ^ 40 * 4851000 * 2
def baseEnd_4851000 : Nat := 2490894654960625673890663

theorem tailTrace_4851000 : CollatzResearch.WordTrace tailWord_4851000 prefixEnd_4851000 2490894654960625673890663 := by
  unfold tailWord_4851000
  simp only [CollatzResearch.WordTrace]
  refine ⟨88465252712831479843031227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117953670283775306457374969 88465252712831479843031227)
  ·
    refine ⟨132697879069247219764546841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88465252712831479843031227 132697879069247219764546841)
    ·
      refine ⟨99523409301935414823410131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132697879069247219764546841 99523409301935414823410131)
      ·
        refine ⟨149285113952903122235115197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99523409301935414823410131 149285113952903122235115197)
        ·
          refine ⟨55981917732338670838168199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149285113952903122235115197 55981917732338670838168199)
          ·
            refine ⟨83972876598508006257252299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55981917732338670838168199 83972876598508006257252299)
            ·
              refine ⟨125959314897762009385878449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83972876598508006257252299 125959314897762009385878449)
              ·
                refine ⟨94469486173321507039408837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125959314897762009385878449 94469486173321507039408837)
                ·
                  refine ⟨17713028657497782569889157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94469486173321507039408837 17713028657497782569889157)
                  ·
                    refine ⟨3321192873280834231854217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17713028657497782569889157 3321192873280834231854217)
                    ·
                      refine ⟨2490894654960625673890663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321192873280834231854217 2490894654960625673890663)
                      ·
                        rfl

theorem cell23_4851000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 4, 2].length) (baseStart_4851000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851000 prefixEnd_4851000 := by exact prefixLift 4851000
  have htrace : WordTrace (prefixWord ++ tailWord_4851000) baseStart_4851000 baseEnd_4851000 := by
    simpa [prefixWord, tailWord_4851000, baseEnd_4851000] using wordTrace_append hprefix tailTrace_4851000
  have hstable : (prefixWord ++ tailWord_4851000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851000).length < 2 ^ (prefixWord ++ tailWord_4851000).sum := by decide
  have hdescent : baseEnd_4851000 < baseStart_4851000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851003 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 3]
def baseStart_4851003 : Nat := 118140960795 + 4851003 * 2 ^ 59
def prefixEnd_4851003 : Nat := 4983230072969 + 3 ^ 40 * 4851003 * 2
def baseEnd_4851003 : Nat := 2490896195402589162153149

theorem tailTrace_4851003 : CollatzResearch.WordTrace tailWord_4851003 prefixEnd_4851003 2490896195402589162153149 := by
  unfold tailWord_4851003
  simp only [CollatzResearch.WordTrace]
  refine ⟨176930614844652091198421663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117953743229768060798947775 176930614844652091198421663)
  ·
    refine ⟨265395922266978136797632495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176930614844652091198421663 265395922266978136797632495)
    ·
      refine ⟨398093883400467205196448743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265395922266978136797632495 398093883400467205196448743)
      ·
        refine ⟨597140825100700807794673115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398093883400467205196448743 597140825100700807794673115)
        ·
          refine ⟨895711237651051211692009673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597140825100700807794673115 895711237651051211692009673)
          ·
            refine ⟨671783428238288408769007255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 895711237651051211692009673 671783428238288408769007255)
            ·
              refine ⟨1007675142357432613153510883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671783428238288408769007255 1007675142357432613153510883)
              ·
                refine ⟨1511512713536148919730266325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1007675142357432613153510883 1511512713536148919730266325)
                ·
                  refine ⟨35426079223503490306178117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1511512713536148919730266325 35426079223503490306178117)
                  ·
                    refine ⟨6642389854406904432408397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35426079223503490306178117 6642389854406904432408397)
                    ·
                      refine ⟨2490896195402589162153149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6642389854406904432408397 2490896195402589162153149)
                      ·
                        rfl

theorem cell23_4851003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 3].length) (baseStart_4851003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851003 prefixEnd_4851003 := by exact prefixLift 4851003
  have htrace : WordTrace (prefixWord ++ tailWord_4851003) baseStart_4851003 baseEnd_4851003 := by
    simpa [prefixWord, tailWord_4851003, baseEnd_4851003] using wordTrace_append hprefix tailTrace_4851003
  have hstable : (prefixWord ++ tailWord_4851003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851003).length < 2 ^ (prefixWord ++ tailWord_4851003).sum := by decide
  have hdescent : baseEnd_4851003 < baseStart_4851003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851027 : List Nat := [1, 1, 1, 2, 1, 1, 7, 4, 1, 4]
def baseStart_4851027 : Nat := 118140960795 + 4851027 * 2 ^ 59
def prefixEnd_4851027 : Nat := 4983230072969 + 3 ^ 40 * 4851027 * 2
def baseEnd_4851027 : Nat := 830302839646099022751013

theorem tailTrace_4851027 : CollatzResearch.WordTrace tailWord_4851027 prefixEnd_4851027 830302839646099022751013 := by
  unfold tailWord_4851027
  simp only [CollatzResearch.WordTrace]
  refine ⟨176931490196565143297295335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117954326797710095531530223 176931490196565143297295335)
  ·
    refine ⟨265397235294847714945943003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176931490196565143297295335 265397235294847714945943003)
    ·
      refine ⟨398095852942271572418914505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265397235294847714945943003 398095852942271572418914505)
      ·
        refine ⟨298571889706703679314185879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 398095852942271572418914505 298571889706703679314185879)
        ·
          refine ⟨447857834560055518971278819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298571889706703679314185879 447857834560055518971278819)
          ·
            refine ⟨671786751840083278456918229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447857834560055518971278819 671786751840083278456918229)
            ·
              refine ⟨15745001996251951838834021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 671786751840083278456918229 15745001996251951838834021)
              ·
                refine ⟨2952187874297240969781379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15745001996251951838834021 2952187874297240969781379)
                ·
                  refine ⟨4428281811445861454672069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952187874297240969781379 4428281811445861454672069)
                  ·
                    refine ⟨830302839646099022751013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4428281811445861454672069 830302839646099022751013)
                    ·
                      rfl

theorem cell23_4851027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 1, 4].length) (baseStart_4851027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851027 prefixEnd_4851027 := by exact prefixLift 4851027
  have htrace : WordTrace (prefixWord ++ tailWord_4851027) baseStart_4851027 baseEnd_4851027 := by
    simpa [prefixWord, tailWord_4851027, baseEnd_4851027] using wordTrace_append hprefix tailTrace_4851027
  have hstable : (prefixWord ++ tailWord_4851027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851027).length < 2 ^ (prefixWord ++ tailWord_4851027).sum := by decide
  have hdescent : baseEnd_4851027 < baseStart_4851027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851040 : List Nat := [2, 1, 1, 3, 4, 1, 2, 3, 6]
def baseStart_4851040 : Nat := 118140960795 + 4851040 * 2 ^ 59
def prefixEnd_4851040 : Nat := 4983230072969 + 3 ^ 40 * 4851040 * 2
def baseEnd_4851040 : Nat := 276768354909645057487831

theorem tailTrace_4851040 : CollatzResearch.WordTrace tailWord_4851040 prefixEnd_4851040 276768354909645057487831 := by
  unfold tailWord_4851040
  simp only [CollatzResearch.WordTrace]
  refine ⟨88465982172759023258759287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117954642897012031011679049 88465982172759023258759287)
  ·
    refine ⟨132698973259138534888138931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88465982172759023258759287 132698973259138534888138931)
    ·
      refine ⟨199048459888707802332208397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132698973259138534888138931 199048459888707802332208397)
      ·
        refine ⟨74643172458265425874578149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199048459888707802332208397 74643172458265425874578149)
        ·
          refine ⟨13995594835924767351483403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74643172458265425874578149 13995594835924767351483403)
          ·
            refine ⟨20993392253887151027225105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13995594835924767351483403 20993392253887151027225105)
            ·
              refine ⟨15745044190415363270418829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20993392253887151027225105 15745044190415363270418829)
              ·
                refine ⟨5904391571405761226407061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15745044190415363270418829 5904391571405761226407061)
                ·
                  refine ⟨276768354909645057487831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5904391571405761226407061 276768354909645057487831)
                  ·
                    rfl

theorem cell23_4851040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 6].length) (baseStart_4851040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851040 prefixEnd_4851040 := by exact prefixLift 4851040
  have htrace : WordTrace (prefixWord ++ tailWord_4851040) baseStart_4851040 baseEnd_4851040 := by
    simpa [prefixWord, tailWord_4851040, baseEnd_4851040] using wordTrace_append hprefix tailTrace_4851040
  have hstable : (prefixWord ++ tailWord_4851040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851040).length < 2 ^ (prefixWord ++ tailWord_4851040).sum := by decide
  have hdescent : baseEnd_4851040 < baseStart_4851040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851054 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_4851054 : Nat := 118140960795 + 4851054 * 2 ^ 59
def prefixEnd_4851054 : Nat := 4983230072969 + 3 ^ 40 * 4851054 * 2
def baseEnd_4851054 : Nat := 2490922382915968462615415

theorem tailTrace_4851054 : CollatzResearch.WordTrace tailWord_4851054 prefixEnd_4851054 2490922382915968462615415 := by
  unfold tailWord_4851054
  simp only [CollatzResearch.WordTrace]
  refine ⟨22116559370933415863566027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117954983311644884605685477 22116559370933415863566027)
  ·
    refine ⟨33174839056400123795349041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22116559370933415863566027 33174839056400123795349041)
    ·
      refine ⟨24881129292300092846511781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33174839056400123795349041 24881129292300092846511781)
      ·
        refine ⟨4665211742306267408720959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24881129292300092846511781 4665211742306267408720959)
        ·
          refine ⟨6997817613459401113081439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4665211742306267408720959 6997817613459401113081439)
          ·
            refine ⟨10496726420189101669622159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6997817613459401113081439 10496726420189101669622159)
            ·
              refine ⟨15745089630283652504433239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10496726420189101669622159 15745089630283652504433239)
              ·
                refine ⟨23617634445425478756649859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15745089630283652504433239 23617634445425478756649859)
                ·
                  refine ⟨35426451668138218134974789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23617634445425478756649859 35426451668138218134974789)
                  ·
                    refine ⟨6642459687775915900307773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35426451668138218134974789 6642459687775915900307773)
                    ·
                      refine ⟨2490922382915968462615415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6642459687775915900307773 2490922382915968462615415)
                      ·
                        rfl

theorem cell23_4851054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_4851054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851054 prefixEnd_4851054 := by exact prefixLift 4851054
  have htrace : WordTrace (prefixWord ++ tailWord_4851054) baseStart_4851054 baseEnd_4851054 := by
    simpa [prefixWord, tailWord_4851054, baseEnd_4851054] using wordTrace_append hprefix tailTrace_4851054
  have hstable : (prefixWord ++ tailWord_4851054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851054).length < 2 ^ (prefixWord ++ tailWord_4851054).sum := by decide
  have hdescent : baseEnd_4851054 < baseStart_4851054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851061 : List Nat := [1, 3, 4, 1, 3, 1, 2, 3, 1, 4]
def baseStart_4851061 : Nat := 118140960795 + 4851061 * 2 ^ 59
def prefixEnd_4851061 : Nat := 4983230072969 + 3 ^ 40 * 4851061 * 2
def baseEnd_4851061 : Nat := 830308659093516645075961

theorem tailTrace_4851061 : CollatzResearch.WordTrace tailWord_4851061 prefixEnd_4851061 830308659093516645075961 := by
  unfold tailWord_4851061
  simp only [CollatzResearch.WordTrace]
  refine ⟨176932730278441967104033037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117955153518961311402688691 176932730278441967104033037)
  ·
    refine ⟨66349773854415737664012389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176932730278441967104033037 66349773854415737664012389)
    ·
      refine ⟨12440582597702950812002323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66349773854415737664012389 12440582597702950812002323)
      ·
        refine ⟨18660873896554426218003485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12440582597702950812002323 18660873896554426218003485)
        ·
          refine ⟨6997827711207909831751307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18660873896554426218003485 6997827711207909831751307)
          ·
            refine ⟨10496741566811864747626961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6997827711207909831751307 10496741566811864747626961)
            ·
              refine ⟨7872556175108898560720221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10496741566811864747626961 7872556175108898560720221)
              ·
                refine ⟨2952208565665836960270083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7872556175108898560720221 2952208565665836960270083)
                ·
                  refine ⟨4428312848498755440405125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952208565665836960270083 4428312848498755440405125)
                  ·
                    refine ⟨830308659093516645075961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4428312848498755440405125 830308659093516645075961)
                    ·
                      rfl

theorem cell23_4851061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_4851061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851061 prefixEnd_4851061 := by exact prefixLift 4851061
  have htrace : WordTrace (prefixWord ++ tailWord_4851061) baseStart_4851061 baseEnd_4851061 := by
    simpa [prefixWord, tailWord_4851061, baseEnd_4851061] using wordTrace_append hprefix tailTrace_4851061
  have hstable : (prefixWord ++ tailWord_4851061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851061).length < 2 ^ (prefixWord ++ tailWord_4851061).sum := by decide
  have hdescent : baseEnd_4851061 < baseStart_4851061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851074 : List Nat := [3, 4, 2, 1, 1, 1, 3, 2, 6]
def baseStart_4851074 : Nat := 118140960795 + 4851074 * 2 ^ 59
def prefixEnd_4851074 : Nat := 4983230072969 + 3 ^ 40 * 4851074 * 2
def baseEnd_4851074 : Nat := 276770294725450931596147

theorem tailTrace_4851074 : CollatzResearch.WordTrace tailWord_4851074 prefixEnd_4851074 276770294725450931596147 := by
  unfold tailWord_4851074
  simp only [CollatzResearch.WordTrace]
  refine ⟨44233301106848717581064069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117955469618263246882837517 44233301106848717581064069)
  ·
    refine ⟨8293743957534134546449513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44233301106848717581064069 8293743957534134546449513)
    ·
      refine ⟨6220307968150600909837135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8293743957534134546449513 6220307968150600909837135)
      ·
        refine ⟨9330461952225901364755703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6220307968150600909837135 9330461952225901364755703)
        ·
          refine ⟨13995692928338852047133555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9330461952225901364755703 13995692928338852047133555)
          ·
            refine ⟨20993539392508278070700333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13995692928338852047133555 20993539392508278070700333)
            ·
              refine ⟨7872577272190604276512625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20993539392508278070700333 7872577272190604276512625)
              ·
                refine ⟨5904432954142953207384469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7872577272190604276512625 5904432954142953207384469)
                ·
                  refine ⟨276770294725450931596147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5904432954142953207384469 276770294725450931596147)
                  ·
                    rfl

theorem cell23_4851074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_4851074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851074 prefixEnd_4851074 := by exact prefixLift 4851074
  have htrace : WordTrace (prefixWord ++ tailWord_4851074) baseStart_4851074 baseEnd_4851074 := by
    simpa [prefixWord, tailWord_4851074, baseEnd_4851074] using wordTrace_append hprefix tailTrace_4851074
  have hstable : (prefixWord ++ tailWord_4851074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851074).length < 2 ^ (prefixWord ++ tailWord_4851074).sum := by decide
  have hdescent : baseEnd_4851074 < baseStart_4851074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851077 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 2, 3, 2]
def baseStart_4851077 : Nat := 118140960795 + 4851077 * 2 ^ 59
def prefixEnd_4851077 : Nat := 4983230072969 + 3 ^ 40 * 4851077 * 2
def baseEnd_4851077 : Nat := 2490934192971021872627809

theorem tailTrace_4851077 : CollatzResearch.WordTrace tailWord_4851077 prefixEnd_4851077 2490934192971021872627809 := by
  unfold tailWord_4851077
  simp only [CollatzResearch.WordTrace]
  refine ⟨176933313846384001836615485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117955542564256001224410323 176933313846384001836615485)
  ·
    refine ⟨66349992692394000688730807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176933313846384001836615485 66349992692394000688730807)
    ·
      refine ⟨99524989038591001033096211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66349992692394000688730807 99524989038591001033096211)
      ·
        refine ⟨149287483557886501549644317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99524989038591001033096211 149287483557886501549644317)
        ·
          refine ⟨55982806334207438081116619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149287483557886501549644317 55982806334207438081116619)
          ·
            refine ⟨83974209501311157121674929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55982806334207438081116619 83974209501311157121674929)
            ·
              refine ⟨62980657125983367841256197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83974209501311157121674929 62980657125983367841256197)
              ·
                refine ⟨11808873211121881470235537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62980657125983367841256197 11808873211121881470235537)
                ·
                  refine ⟨8856654908341411102676653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11808873211121881470235537 8856654908341411102676653)
                  ·
                    refine ⟨3321245590628029163503745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8856654908341411102676653 3321245590628029163503745)
                    ·
                      refine ⟨2490934192971021872627809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321245590628029163503745 2490934192971021872627809)
                      ·
                        rfl

theorem cell23_4851077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 3, 2].length) (baseStart_4851077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851077 prefixEnd_4851077 := by exact prefixLift 4851077
  have htrace : WordTrace (prefixWord ++ tailWord_4851077) baseStart_4851077 baseEnd_4851077 := by
    simpa [prefixWord, tailWord_4851077, baseEnd_4851077] using wordTrace_append hprefix tailTrace_4851077
  have hstable : (prefixWord ++ tailWord_4851077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851077).length < 2 ^ (prefixWord ++ tailWord_4851077).sum := by decide
  have hdescent : baseEnd_4851077 < baseStart_4851077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851084 : List Nat := [2, 2, 1, 2, 1, 3, 1, 6, 1, 1, 3]
def baseStart_4851084 : Nat := 118140960795 + 4851084 * 2 ^ 59
def prefixEnd_4851084 : Nat := 4983230072969 + 3 ^ 40 * 4851084 * 2
def baseEnd_4851084 : Nat := 2490937787335603345240277

theorem tailTrace_4851084 : CollatzResearch.WordTrace tailWord_4851084 prefixEnd_4851084 2490937787335603345240277 := by
  unfold tailWord_4851084
  simp only [CollatzResearch.WordTrace]
  refine ⟨88466784578679321016060153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117955712771572428021413537 88466784578679321016060153)
  ·
    refine ⟨66350088434009490762045115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88466784578679321016060153 66350088434009490762045115)
    ·
      refine ⟨99525132651014236143067673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66350088434009490762045115 99525132651014236143067673)
      ·
        refine ⟨74643849488260677107300755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99525132651014236143067673 74643849488260677107300755)
        ·
          refine ⟨111965774232391015660951133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74643849488260677107300755 111965774232391015660951133)
          ·
            refine ⟨41987165337146630872856675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111965774232391015660951133 41987165337146630872856675)
            ·
              refine ⟨62980748005719946309285013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41987165337146630872856675 62980748005719946309285013)
              ·
                refine ⟨2952222562768122483247735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62980748005719946309285013 2952222562768122483247735)
                ·
                  refine ⟨4428333844152183724871603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952222562768122483247735 4428333844152183724871603)
                  ·
                    refine ⟨6642500766228275587307405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4428333844152183724871603 6642500766228275587307405)
                    ·
                      refine ⟨2490937787335603345240277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6642500766228275587307405 2490937787335603345240277)
                      ·
                        rfl

theorem cell23_4851084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_4851084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851084 prefixEnd_4851084 := by exact prefixLift 4851084
  have htrace : WordTrace (prefixWord ++ tailWord_4851084) baseStart_4851084 baseEnd_4851084 := by
    simpa [prefixWord, tailWord_4851084, baseEnd_4851084] using wordTrace_append hprefix tailTrace_4851084
  have hstable : (prefixWord ++ tailWord_4851084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851084).length < 2 ^ (prefixWord ++ tailWord_4851084).sum := by decide
  have hdescent : baseEnd_4851084 < baseStart_4851084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851107 : List Nat := [1, 1, 1, 4, 1, 3, 4, 2, 1, 1, 4]
def baseStart_4851107 : Nat := 118140960795 + 4851107 * 2 ^ 59
def prefixEnd_4851107 : Nat := 4983230072969 + 3 ^ 40 * 4851107 * 2
def baseEnd_4851107 : Nat := 2490949597390656755252671

theorem tailTrace_4851107 : CollatzResearch.WordTrace tailWord_4851107 prefixEnd_4851107 2490949597390656755252671 := by
  unfold tailWord_4851107
  simp only [CollatzResearch.WordTrace]
  refine ⟨176934408036275316960207575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117956272024183544640138383 176934408036275316960207575)
  ·
    refine ⟨265401612054412975440311363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176934408036275316960207575 265401612054412975440311363)
    ·
      refine ⟨398102418081619463160467045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265401612054412975440311363 398102418081619463160467045)
      ·
        refine ⟨74644203390303649342587571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 398102418081619463160467045 74644203390303649342587571)
        ·
          refine ⟨111966305085455474013881357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74644203390303649342587571 111966305085455474013881357)
          ·
            refine ⟨41987364407045802755205509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111966305085455474013881357 41987364407045802755205509)
            ·
              refine ⟨7872630826321088016601033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41987364407045802755205509 7872630826321088016601033)
              ·
                refine ⟨5904473119740816012450775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7872630826321088016601033 5904473119740816012450775)
                ·
                  refine ⟨8856709679611224018676163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5904473119740816012450775 8856709679611224018676163)
                  ·
                    refine ⟨13285064519416836028014245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8856709679611224018676163 13285064519416836028014245)
                    ·
                      refine ⟨2490949597390656755252671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13285064519416836028014245 2490949597390656755252671)
                      ·
                        rfl

theorem cell23_4851107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_4851107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851107 prefixEnd_4851107 := by exact prefixLift 4851107
  have htrace : WordTrace (prefixWord ++ tailWord_4851107) baseStart_4851107 baseEnd_4851107 := by
    simpa [prefixWord, tailWord_4851107, baseEnd_4851107] using wordTrace_append hprefix tailTrace_4851107
  have hstable : (prefixWord ++ tailWord_4851107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851107).length < 2 ^ (prefixWord ++ tailWord_4851107).sum := by decide
  have hdescent : baseEnd_4851107 < baseStart_4851107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851127 : List Nat := [1, 1, 3, 1, 3, 2, 1, 5, 1, 2, 3]
def baseStart_4851127 : Nat := 118140960795 + 4851127 * 2 ^ 59
def prefixEnd_4851127 : Nat := 4983230072969 + 3 ^ 40 * 4851127 * 2
def baseEnd_4851127 : Nat := 2490959867003746677002579

theorem tailTrace_4851127 : CollatzResearch.WordTrace tailWord_4851127 prefixEnd_4851127 2490959867003746677002579 := by
  unfold tailWord_4851127
  simp only [CollatzResearch.WordTrace]
  refine ⟨176935137496202860375935635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117956758330801906917290423 176935137496202860375935635)
  ·
    refine ⟨265402706244304290563903453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176935137496202860375935635 265402706244304290563903453)
    ·
      refine ⟨99526014841614108961463795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265402706244304290563903453 99526014841614108961463795)
      ·
        refine ⟨149289022262421163442195693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99526014841614108961463795 149289022262421163442195693)
        ·
          refine ⟨55983383348407936290823385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149289022262421163442195693 55983383348407936290823385)
          ·
            refine ⟨41987537511305952218117539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55983383348407936290823385 41987537511305952218117539)
            ·
              refine ⟨62981306266958928327176309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41987537511305952218117539 62981306266958928327176309)
              ·
                refine ⟨5904497462527399530672779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62981306266958928327176309 5904497462527399530672779)
                ·
                  refine ⟨8856746193791099296009169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5904497462527399530672779 8856746193791099296009169)
                  ·
                    refine ⟨6642559645343324472006877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8856746193791099296009169 6642559645343324472006877)
                    ·
                      refine ⟨2490959867003746677002579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6642559645343324472006877 2490959867003746677002579)
                      ·
                        rfl

theorem cell23_4851127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_4851127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851127 prefixEnd_4851127 := by exact prefixLift 4851127
  have htrace : WordTrace (prefixWord ++ tailWord_4851127) baseStart_4851127 baseEnd_4851127 := by
    simpa [prefixWord, tailWord_4851127, baseEnd_4851127] using wordTrace_append hprefix tailTrace_4851127
  have hstable : (prefixWord ++ tailWord_4851127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851127).length < 2 ^ (prefixWord ++ tailWord_4851127).sum := by decide
  have hdescent : baseEnd_4851127 < baseStart_4851127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851157 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_4851157 : Nat := 118140960795 + 4851157 * 2 ^ 59
def prefixEnd_4851157 : Nat := 4983230072969 + 3 ^ 40 * 4851157 * 2
def baseEnd_4851157 : Nat := 2490975271423381559627441

theorem tailTrace_4851157 : CollatzResearch.WordTrace tailWord_4851157 prefixEnd_4851157 2490975271423381559627441 := by
  unfold tailWord_4851157
  simp only [CollatzResearch.WordTrace]
  refine ⟨176936231686094175499527725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117957487790729450333018483 176936231686094175499527725)
  ·
    refine ⟨66351086882285315812322897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176936231686094175499527725 66351086882285315812322897)
    ·
      refine ⟨49763315161713986859242173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66351086882285315812322897 49763315161713986859242173)
      ·
        refine ⟨18661243185642745072215815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49763315161713986859242173 18661243185642745072215815)
        ·
          refine ⟨27991864778464117608323723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18661243185642745072215815 27991864778464117608323723)
          ·
            refine ⟨41987797167696176412485585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27991864778464117608323723 41987797167696176412485585)
            ·
              refine ⟨31490847875772132309364189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41987797167696176412485585 31490847875772132309364189)
              ·
                refine ⟨11809067953414549616011571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31490847875772132309364189 11809067953414549616011571)
                ·
                  refine ⟨17713601930121824424017357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11809067953414549616011571 17713601930121824424017357)
                  ·
                    refine ⟨6642600723795684159006509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17713601930121824424017357 6642600723795684159006509)
                    ·
                      refine ⟨2490975271423381559627441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6642600723795684159006509 2490975271423381559627441)
                      ·
                        rfl

theorem cell23_4851157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_4851157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851157 prefixEnd_4851157 := by exact prefixLift 4851157
  have htrace : WordTrace (prefixWord ++ tailWord_4851157) baseStart_4851157 baseEnd_4851157 := by
    simpa [prefixWord, tailWord_4851157, baseEnd_4851157] using wordTrace_append hprefix tailTrace_4851157
  have hstable : (prefixWord ++ tailWord_4851157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851157).length < 2 ^ (prefixWord ++ tailWord_4851157).sum := by decide
  have hdescent : baseEnd_4851157 < baseStart_4851157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851207 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 2, 6]
def baseStart_4851207 : Nat := 118140960795 + 4851207 * 2 ^ 59
def prefixEnd_4851207 : Nat := 4983230072969 + 3 ^ 40 * 4851207 * 2
def baseEnd_4851207 : Nat := 830333648485368788000737

theorem tailTrace_4851207 : CollatzResearch.WordTrace tailWord_4851207 prefixEnd_4851207 830333648485368788000737 := by
  unfold tailWord_4851207
  simp only [CollatzResearch.WordTrace]
  refine ⟨176938055335913034038847875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117958703557275356025898583 176938055335913034038847875)
  ·
    refine ⟨265407083003869551058271813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176938055335913034038847875 265407083003869551058271813)
    ·
      refine ⟨49763828063225540823425965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265407083003869551058271813 49763828063225540823425965)
      ·
        refine ⟨18661435523709577808784737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49763828063225540823425965 18661435523709577808784737)
        ·
          refine ⟨13996076642782183356588553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18661435523709577808784737 13996076642782183356588553)
          ·
            refine ⟨10497057482086637517441415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13996076642782183356588553 10497057482086637517441415)
            ·
              refine ⟨15745586223129956276162123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10497057482086637517441415 15745586223129956276162123)
              ·
                refine ⟨23618379334694934414243185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15745586223129956276162123 23618379334694934414243185)
                ·
                  refine ⟨17713784501021200810682389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23618379334694934414243185 17713784501021200810682389)
                  ·
                    refine ⟨830333648485368788000737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17713784501021200810682389 830333648485368788000737)
                    ·
                      rfl

theorem cell23_4851207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_4851207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851207 prefixEnd_4851207 := by exact prefixLift 4851207
  have htrace : WordTrace (prefixWord ++ tailWord_4851207) baseStart_4851207 baseEnd_4851207 := by
    simpa [prefixWord, tailWord_4851207, baseEnd_4851207] using wordTrace_append hprefix tailTrace_4851207
  have hstable : (prefixWord ++ tailWord_4851207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851207).length < 2 ^ (prefixWord ++ tailWord_4851207).sum := by decide
  have hdescent : baseEnd_4851207 < baseStart_4851207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851235 : List Nat := [1, 1, 1, 4, 6, 1, 2, 1, 1, 3, 2]
def baseStart_4851235 : Nat := 118140960795 + 4851235 * 2 ^ 59
def prefixEnd_4851235 : Nat := 4983230072969 + 3 ^ 40 * 4851235 * 2
def baseEnd_4851235 : Nat := 2491015322914432254452083

theorem tailTrace_4851235 : CollatzResearch.WordTrace tailWord_4851235 prefixEnd_4851235 2491015322914432254452083 := by
  unfold tailWord_4851235
  simp only [CollatzResearch.WordTrace]
  refine ⟨176939076579811594820867159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117959384386541063213911439 176939076579811594820867159)
  ·
    refine ⟨265408614869717392231300739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176939076579811594820867159 265408614869717392231300739)
    ·
      refine ⟨398112922304576088346951109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265408614869717392231300739 398112922304576088346951109)
      ·
        refine ⟨74646172932108016565053333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 398112922304576088346951109 74646172932108016565053333)
        ·
          refine ⟨3499039356192563276486875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74646172932108016565053333 3499039356192563276486875)
          ·
            refine ⟨5248559034288844914730313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3499039356192563276486875 5248559034288844914730313)
            ·
              refine ⟨3936419275716633686047735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5248559034288844914730313 3936419275716633686047735)
              ·
                refine ⟨5904628913574950529071603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3936419275716633686047735 5904628913574950529071603)
                ·
                  refine ⟨8856943370362425793607405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5904628913574950529071603 8856943370362425793607405)
                  ·
                    refine ⟨3321353763885909672602777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8856943370362425793607405 3321353763885909672602777)
                    ·
                      refine ⟨2491015322914432254452083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321353763885909672602777 2491015322914432254452083)
                      ·
                        rfl

theorem cell23_4851235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_4851235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851235 prefixEnd_4851235 := by exact prefixLift 4851235
  have htrace : WordTrace (prefixWord ++ tailWord_4851235) baseStart_4851235 baseEnd_4851235 := by
    simpa [prefixWord, tailWord_4851235, baseEnd_4851235] using wordTrace_append hprefix tailTrace_4851235
  have hstable : (prefixWord ++ tailWord_4851235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851235).length < 2 ^ (prefixWord ++ tailWord_4851235).sum := by decide
  have hdescent : baseEnd_4851235 < baseStart_4851235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851280 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 2, 8]
def baseStart_4851280 : Nat := 118140960795 + 4851280 * 2 ^ 59
def prefixEnd_4851280 : Nat := 4983230072969 + 3 ^ 40 * 4851280 * 2
def baseEnd_4851280 : Nat := 830346143181294859463125

theorem tailTrace_4851280 : CollatzResearch.WordTrace tailWord_4851280 prefixEnd_4851280 830346143181294859463125 := by
  unfold tailWord_4851280
  simp only [CollatzResearch.WordTrace]
  refine ⟨88470358932324283753127647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117960478576432378337503529 88470358932324283753127647)
  ·
    refine ⟨132705538398486425629691471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88470358932324283753127647 132705538398486425629691471)
    ·
      refine ⟨199058307597729638444537207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132705538398486425629691471 199058307597729638444537207)
      ·
        refine ⟨298587461396594457666805811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199058307597729638444537207 298587461396594457666805811)
        ·
          refine ⟨447881192094891686500208717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298587461396594457666805811 447881192094891686500208717)
          ·
            refine ⟨167955447035584382437578269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 447881192094891686500208717 167955447035584382437578269)
            ·
              refine ⟨62983292638344143414091851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167955447035584382437578269 62983292638344143414091851)
              ·
                refine ⟨94474938957516215121137777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62983292638344143414091851 94474938957516215121137777)
                ·
                  refine ⟨70856204218137161340853333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94474938957516215121137777 70856204218137161340853333)
                  ·
                    refine ⟨830346143181294859463125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70856204218137161340853333 830346143181294859463125)
                    ·
                      rfl

theorem cell23_4851280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_4851280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851280 prefixEnd_4851280 := by exact prefixLift 4851280
  have htrace : WordTrace (prefixWord ++ tailWord_4851280) baseStart_4851280 baseEnd_4851280 := by
    simpa [prefixWord, tailWord_4851280, baseEnd_4851280] using wordTrace_append hprefix tailTrace_4851280
  have hstable : (prefixWord ++ tailWord_4851280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851280).length < 2 ^ (prefixWord ++ tailWord_4851280).sum := by decide
  have hdescent : baseEnd_4851280 < baseStart_4851280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851287 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 4]
def baseStart_4851287 : Nat := 118140960795 + 4851287 * 2 ^ 59
def prefixEnd_4851287 : Nat := 4983230072969 + 3 ^ 40 * 4851287 * 2
def baseEnd_4851287 : Nat := 2491042023908466051001843

theorem tailTrace_4851287 : CollatzResearch.WordTrace tailWord_4851287 prefixEnd_4851287 2491042023908466051001843 := by
  unfold tailWord_4851287
  simp only [CollatzResearch.WordTrace]
  refine ⟨176940973175623207701760115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117960648783748805134506743 176940973175623207701760115)
  ·
    refine ⟨265411459763434811552640173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176940973175623207701760115 265411459763434811552640173)
    ·
      refine ⟨99529297411288054332240065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265411459763434811552640173 99529297411288054332240065)
      ·
        refine ⟨74646973058466040749180049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99529297411288054332240065 74646973058466040749180049)
        ·
          refine ⟨55985229793849530561885037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74646973058466040749180049 55985229793849530561885037)
          ·
            refine ⟨20994461172693573960706889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55985229793849530561885037 20994461172693573960706889)
            ·
              refine ⟨15745845879520180470530167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20994461172693573960706889 15745845879520180470530167)
              ·
                refine ⟨23618768819280270705795251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15745845879520180470530167 23618768819280270705795251)
                ·
                  refine ⟨35428153228920406058692877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23618768819280270705795251 35428153228920406058692877)
                  ·
                    refine ⟨13285557460845152272009829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35428153228920406058692877 13285557460845152272009829)
                    ·
                      refine ⟨2491042023908466051001843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13285557460845152272009829 2491042023908466051001843)
                      ·
                        rfl

theorem cell23_4851287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_4851287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851287 prefixEnd_4851287 := by exact prefixLift 4851287
  have htrace : WordTrace (prefixWord ++ tailWord_4851287) baseStart_4851287 baseEnd_4851287 := by
    simpa [prefixWord, tailWord_4851287, baseEnd_4851287] using wordTrace_append hprefix tailTrace_4851287
  have hstable : (prefixWord ++ tailWord_4851287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851287).length < 2 ^ (prefixWord ++ tailWord_4851287).sum := by decide
  have hdescent : baseEnd_4851287 < baseStart_4851287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851304 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_4851304 : Nat := 118140960795 + 4851304 * 2 ^ 59
def prefixEnd_4851304 : Nat := 4983230072969 + 3 ^ 40 * 4851304 * 2
def baseEnd_4851304 : Nat := 2491050753079592484489265

theorem tailTrace_4851304 : CollatzResearch.WordTrace tailWord_4851304 prefixEnd_4851304 2491050753079592484489265 := by
  unfold tailWord_4851304
  simp only [CollatzResearch.WordTrace]
  refine ⟨88470796608280809802564483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117961062144374413070085977 88470796608280809802564483)
  ·
    refine ⟨132706194912421214703846725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88470796608280809802564483 132706194912421214703846725)
    ·
      refine ⟨24882411546078977756971261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132706194912421214703846725 24882411546078977756971261)
      ·
        refine ⟨9330904329779616658864223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24882411546078977756971261 9330904329779616658864223)
        ·
          refine ⟨13996356494669424988296335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9330904329779616658864223 13996356494669424988296335)
          ·
            refine ⟨20994534742004137482444503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13996356494669424988296335 20994534742004137482444503)
            ·
              refine ⟨31491802113006206223666755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20994534742004137482444503 31491802113006206223666755)
              ·
                refine ⟨47237703169509309335500133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31491802113006206223666755 47237703169509309335500133)
                ·
                  refine ⟨8857069344282995500406275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47237703169509309335500133 8857069344282995500406275)
                  ·
                    refine ⟨13285604016424493250609413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8857069344282995500406275 13285604016424493250609413)
                    ·
                      refine ⟨2491050753079592484489265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13285604016424493250609413 2491050753079592484489265)
                      ·
                        rfl

theorem cell23_4851304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_4851304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851304 prefixEnd_4851304 := by exact prefixLift 4851304
  have htrace : WordTrace (prefixWord ++ tailWord_4851304) baseStart_4851304 baseEnd_4851304 := by
    simpa [prefixWord, tailWord_4851304, baseEnd_4851304] using wordTrace_append hprefix tailTrace_4851304
  have hstable : (prefixWord ++ tailWord_4851304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851304).length < 2 ^ (prefixWord ++ tailWord_4851304).sum := by decide
  have hdescent : baseEnd_4851304 < baseStart_4851304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851337 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 2, 5, 3]
def baseStart_4851337 : Nat := 118140960795 + 4851337 * 2 ^ 59
def prefixEnd_4851337 : Nat := 4983230072969 + 3 ^ 40 * 4851337 * 2
def baseEnd_4851337 : Nat := 2491067697941190855376613

theorem tailTrace_4851337 : CollatzResearch.WordTrace tailWord_4851337 prefixEnd_4851337 2491067697941190855376613 := by
  unfold tailWord_4851337
  simp only [CollatzResearch.WordTrace]
  refine ⟨176942796825442066241080265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117961864550294710827386843 176942796825442066241080265)
  ·
    refine ⟨132707097619081549680810199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176942796825442066241080265 132707097619081549680810199)
    ·
      refine ⟨199060646428622324521215299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132707097619081549680810199 199060646428622324521215299)
      ·
        refine ⟨298590969642933486781822949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199060646428622324521215299 298590969642933486781822949)
        ·
          refine ⟨55985806808050028771591803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 298590969642933486781822949 55985806808050028771591803)
          ·
            refine ⟨83978710212075043157387705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55985806808050028771591803 83978710212075043157387705)
            ·
              refine ⟨62984032659056282368040779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83978710212075043157387705 62984032659056282368040779)
              ·
                refine ⟨94476048988584423552061169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62984032659056282368040779 94476048988584423552061169)
                ·
                  refine ⟨70857036741438317664045877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94476048988584423552061169 70857036741438317664045877)
                  ·
                    refine ⟨6642847194509842281004301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70857036741438317664045877 6642847194509842281004301)
                    ·
                      refine ⟨2491067697941190855376613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6642847194509842281004301 2491067697941190855376613)
                      ·
                        rfl

theorem cell23_4851337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 5, 3].length) (baseStart_4851337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851337 prefixEnd_4851337 := by exact prefixLift 4851337
  have htrace : WordTrace (prefixWord ++ tailWord_4851337) baseStart_4851337 baseEnd_4851337 := by
    simpa [prefixWord, tailWord_4851337, baseEnd_4851337] using wordTrace_append hprefix tailTrace_4851337
  have hstable : (prefixWord ++ tailWord_4851337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851337).length < 2 ^ (prefixWord ++ tailWord_4851337).sum := by decide
  have hdescent : baseEnd_4851337 < baseStart_4851337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851397 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_4851397 : Nat := 118140960795 + 4851397 * 2 ^ 59
def prefixEnd_4851397 : Nat := 4983230072969 + 3 ^ 40 * 4851397 * 2
def baseEnd_4851397 : Nat := 2491098506780460620626337

theorem tailTrace_4851397 : CollatzResearch.WordTrace tailWord_4851397 prefixEnd_4851397 2491098506780460620626337 := by
  unfold tailWord_4851397
  simp only [CollatzResearch.WordTrace]
  refine ⟨176944985205224696488264445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117963323470149797658842963 176944985205224696488264445)
  ·
    refine ⟨66354369451959261183099167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176944985205224696488264445 66354369451959261183099167)
    ·
      refine ⟨99531554177938891774648751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66354369451959261183099167 99531554177938891774648751)
      ·
        refine ⟨149297331266908337661973127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99531554177938891774648751 149297331266908337661973127)
        ·
          refine ⟨223945996900362506492959691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149297331266908337661973127 223945996900362506492959691)
          ·
            refine ⟨335918995350543759739439537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223945996900362506492959691 335918995350543759739439537)
            ·
              refine ⟨251939246512907819804579653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335918995350543759739439537 251939246512907819804579653)
              ·
                refine ⟨47238608721170216213358685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251939246512907819804579653 47238608721170216213358685)
                ·
                  refine ⟨17714478270438831080009507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47238608721170216213358685 17714478270438831080009507)
                  ·
                    refine ⟨26571717405658246620014261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17714478270438831080009507 26571717405658246620014261)
                    ·
                      refine ⟨2491098506780460620626337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26571717405658246620014261 2491098506780460620626337)
                      ·
                        rfl

theorem cell23_4851397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_4851397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851397 prefixEnd_4851397 := by exact prefixLift 4851397
  have htrace : WordTrace (prefixWord ++ tailWord_4851397) baseStart_4851397 baseEnd_4851397 := by
    simpa [prefixWord, tailWord_4851397, baseEnd_4851397] using wordTrace_append hprefix tailTrace_4851397
  have hstable : (prefixWord ++ tailWord_4851397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851397).length < 2 ^ (prefixWord ++ tailWord_4851397).sum := by decide
  have hdescent : baseEnd_4851397 < baseStart_4851397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851417 : List Nat := [1, 2, 1, 2, 3, 4, 10]
def baseStart_4851417 : Nat := 118140960795 + 4851417 * 2 ^ 59
def prefixEnd_4851417 : Nat := 4983230072969 + 3 ^ 40 * 4851417 * 2
def baseEnd_4851417 : Nat := 30754429338191982004645

theorem tailTrace_4851417 : CollatzResearch.WordTrace tailWord_4851417 prefixEnd_4851417 30754429338191982004645 := by
  unfold tailWord_4851417
  simp only [CollatzResearch.WordTrace]
  refine ⟨176945714665152239903992505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117963809776768159935995003 176945714665152239903992505)
  ·
    refine ⟨132709285998864179927994379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176945714665152239903992505 132709285998864179927994379)
    ·
      refine ⟨199063928998296269891991569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132709285998864179927994379 199063928998296269891991569)
      ·
        refine ⟨149297946748722202418993677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199063928998296269891991569 149297946748722202418993677)
        ·
          refine ⟨55986730030770825907122629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149297946748722202418993677 55986730030770825907122629)
          ·
            refine ⟨10497511880769529857585493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55986730030770825907122629 10497511880769529857585493)
            ·
              refine ⟨30754429338191982004645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10497511880769529857585493 30754429338191982004645)
              ·
                rfl

theorem cell23_4851417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 10].length) (baseStart_4851417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851417 prefixEnd_4851417 := by exact prefixLift 4851417
  have htrace : WordTrace (prefixWord ++ tailWord_4851417) baseStart_4851417 baseEnd_4851417 := by
    simpa [prefixWord, tailWord_4851417, baseEnd_4851417] using wordTrace_append hprefix tailTrace_4851417
  have hstable : (prefixWord ++ tailWord_4851417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851417).length < 2 ^ (prefixWord ++ tailWord_4851417).sum := by decide
  have hdescent : baseEnd_4851417 < baseStart_4851417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851428 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 3, 2, 2]
def baseStart_4851428 : Nat := 118140960795 + 4851428 * 2 ^ 59
def prefixEnd_4851428 : Nat := 4983230072969 + 3 ^ 40 * 4851428 * 2
def baseEnd_4851428 : Nat := 2491114424680749999338695

theorem tailTrace_4851428 : CollatzResearch.WordTrace tailWord_4851428 prefixEnd_4851428 2491114424680749999338695 := by
  unfold tailWord_4851428
  simp only [CollatzResearch.WordTrace]
  refine ⟨88473057934056194391321469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117964077245408259188428625 88473057934056194391321469)
  ·
    refine ⟨33177396725271072896745551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88473057934056194391321469 33177396725271072896745551)
    ·
      refine ⟨49766095087906609345118327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33177396725271072896745551 49766095087906609345118327)
      ·
        refine ⟨74649142631859914017677491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49766095087906609345118327 74649142631859914017677491)
        ·
          refine ⟨111973713947789871026516237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74649142631859914017677491 111973713947789871026516237)
          ·
            refine ⟨41990142730421201634943589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111973713947789871026516237 41990142730421201634943589)
            ·
              refine ⟨7873151761953975306551923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41990142730421201634943589 7873151761953975306551923)
              ·
                refine ⟨11809727642930962959827885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7873151761953975306551923 11809727642930962959827885)
                ·
                  refine ⟨4428647866099111109935457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11809727642930962959827885 4428647866099111109935457)
                  ·
                    refine ⟨3321485899574333332451593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4428647866099111109935457 3321485899574333332451593)
                    ·
                      refine ⟨2491114424680749999338695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321485899574333332451593 2491114424680749999338695)
                      ·
                        rfl

theorem cell23_4851428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_4851428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851428 prefixEnd_4851428 := by exact prefixLift 4851428
  have htrace : WordTrace (prefixWord ++ tailWord_4851428) baseStart_4851428 baseEnd_4851428 := by
    simpa [prefixWord, tailWord_4851428, baseEnd_4851428] using wordTrace_append hprefix tailTrace_4851428
  have hstable : (prefixWord ++ tailWord_4851428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851428).length < 2 ^ (prefixWord ++ tailWord_4851428).sum := by decide
  have hdescent : baseEnd_4851428 < baseStart_4851428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851438 : List Nat := [4, 1, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_4851438 : Nat := 118140960795 + 4851438 * 2 ^ 59
def prefixEnd_4851438 : Nat := 4983230072969 + 3 ^ 40 * 4851438 * 2
def baseEnd_4851438 : Nat := 830373186495764986737883

theorem tailTrace_4851438 : CollatzResearch.WordTrace tailWord_4851438 prefixEnd_4851438 830373186495764986737883 := by
  unfold tailWord_4851438
  simp only [CollatzResearch.WordTrace]
  refine ⟨22118310074759520061313371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117964320398717440327004645 22118310074759520061313371)
  ·
    refine ⟨33177465112139280091970057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22118310074759520061313371 33177465112139280091970057)
    ·
      refine ⟨24883098834104460068977543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33177465112139280091970057 24883098834104460068977543)
      ·
        refine ⟨37324648251156690103466315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24883098834104460068977543 37324648251156690103466315)
        ·
          refine ⟨55986972376735035155199473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37324648251156690103466315 55986972376735035155199473)
          ·
            refine ⟨41990229282551276366399605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55986972376735035155199473 41990229282551276366399605)
            ·
              refine ⟨3936583995239182159349963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41990229282551276366399605 3936583995239182159349963)
              ·
                refine ⟨5904875992858773239024945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3936583995239182159349963 5904875992858773239024945)
                ·
                  refine ⟨4428656994644079929268709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5904875992858773239024945 4428656994644079929268709)
                  ·
                    refine ⟨830373186495764986737883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4428656994644079929268709 830373186495764986737883)
                    ·
                      rfl

theorem cell23_4851438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_4851438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851438 prefixEnd_4851438 := by exact prefixLift 4851438
  have htrace : WordTrace (prefixWord ++ tailWord_4851438) baseStart_4851438 baseEnd_4851438 := by
    simpa [prefixWord, tailWord_4851438, baseEnd_4851438] using wordTrace_append hprefix tailTrace_4851438
  have hstable : (prefixWord ++ tailWord_4851438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851438).length < 2 ^ (prefixWord ++ tailWord_4851438).sum := by decide
  have hdescent : baseEnd_4851438 < baseStart_4851438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851441 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 1, 2, 4]
def baseStart_4851441 : Nat := 118140960795 + 4851441 * 2 ^ 59
def prefixEnd_4851441 : Nat := 4983230072969 + 3 ^ 40 * 4851441 * 2
def baseEnd_4851441 : Nat := 2491121099929258448476135

theorem tailTrace_4851441 : CollatzResearch.WordTrace tailWord_4851441 prefixEnd_4851441 2491121099929258448476135 := by
  unfold tailWord_4851441
  simp only [CollatzResearch.WordTrace]
  refine ⟨176946590017065292002866177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117964393344710194668577451 176946590017065292002866177)
  ·
    refine ⟨132709942512798969002149633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176946590017065292002866177 132709942512798969002149633)
    ·
      refine ⟨99532456884599226751612225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132709942512798969002149633 99532456884599226751612225)
      ·
        refine ⟨74649342663449420063709169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99532456884599226751612225 74649342663449420063709169)
        ·
          refine ⟨55987006997587065047781877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74649342663449420063709169 55987006997587065047781877)
          ·
            refine ⟨5248781906023787348229551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55987006997587065047781877 5248781906023787348229551)
            ·
              refine ⟨7873172859035681022344327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5248781906023787348229551 7873172859035681022344327)
              ·
                refine ⟨11809759288553521533516491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7873172859035681022344327 11809759288553521533516491)
                ·
                  refine ⟨17714638932830282300274737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11809759288553521533516491 17714638932830282300274737)
                  ·
                    refine ⟨13285979199622711725206053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17714638932830282300274737 13285979199622711725206053)
                    ·
                      refine ⟨2491121099929258448476135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13285979199622711725206053 2491121099929258448476135)
                      ·
                        rfl

theorem cell23_4851441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_4851441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851441 prefixEnd_4851441 := by exact prefixLift 4851441
  have htrace : WordTrace (prefixWord ++ tailWord_4851441) baseStart_4851441 baseEnd_4851441 := by
    simpa [prefixWord, tailWord_4851441, baseEnd_4851441] using wordTrace_append hprefix tailTrace_4851441
  have hstable : (prefixWord ++ tailWord_4851441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851441).length < 2 ^ (prefixWord ++ tailWord_4851441).sum := by decide
  have hdescent : baseEnd_4851441 < baseStart_4851441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851447 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 2, 7]
def baseStart_4851447 : Nat := 118140960795 + 4851447 * 2 ^ 59
def prefixEnd_4851447 : Nat := 4983230072969 + 3 ^ 40 * 4851447 * 2
def baseEnd_4851447 : Nat := 830374726937728475000369

theorem tailTrace_4851447 : CollatzResearch.WordTrace tailWord_4851447 prefixEnd_4851447 830374726937728475000369 := by
  unfold tailWord_4851447
  simp only [CollatzResearch.WordTrace]
  refine ⟨176946808855043555027584595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117964539236695703351723063 176946808855043555027584595)
  ·
    refine ⟨265420213282565332541376893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176946808855043555027584595 265420213282565332541376893)
    ·
      refine ⟨99532579980961999703016335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265420213282565332541376893 99532579980961999703016335)
      ·
        refine ⟨149298869971442999554524503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99532579980961999703016335 149298869971442999554524503)
        ·
          refine ⟨223948304957164499331786755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149298869971442999554524503 223948304957164499331786755)
          ·
            refine ⟨335922457435746748997680133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223948304957164499331786755 335922457435746748997680133)
            ·
              refine ⟨62985460769202515437065025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 335922457435746748997680133 62985460769202515437065025)
              ·
                refine ⟨47239095576901886577798769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62985460769202515437065025 47239095576901886577798769)
                ·
                  refine ⟨35429321682676414933349077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47239095576901886577798769 35429321682676414933349077)
                  ·
                    refine ⟨830374726937728475000369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35429321682676414933349077 830374726937728475000369)
                    ·
                      rfl

theorem cell23_4851447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 7].length) (baseStart_4851447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851447 prefixEnd_4851447 := by exact prefixLift 4851447
  have htrace : WordTrace (prefixWord ++ tailWord_4851447) baseStart_4851447 baseEnd_4851447 := by
    simpa [prefixWord, tailWord_4851447, baseEnd_4851447] using wordTrace_append hprefix tailTrace_4851447
  have hstable : (prefixWord ++ tailWord_4851447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851447).length < 2 ^ (prefixWord ++ tailWord_4851447).sum := by decide
  have hdescent : baseEnd_4851447 < baseStart_4851447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851484 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_4851484 : Nat := 118140960795 + 4851484 * 2 ^ 59
def prefixEnd_4851484 : Nat := 4983230072969 + 3 ^ 40 * 4851484 * 2
def baseEnd_4851484 : Nat := 2491143179597401780238437

theorem tailTrace_4851484 : CollatzResearch.WordTrace tailWord_4851484 prefixEnd_4851484 2491143179597401780238437 := by
  unfold tailWord_4851484
  simp only [CollatzResearch.WordTrace]
  refine ⟨88474079177954755173340753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117965438903939673564454337 88474079177954755173340753)
  ·
    refine ⟨66355559383466066380005565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88474079177954755173340753 66355559383466066380005565)
    ·
      refine ⟨24883334768799774892502087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66355559383466066380005565 24883334768799774892502087)
      ·
        refine ⟨37325002153199662338753131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24883334768799774892502087 37325002153199662338753131)
        ·
          refine ⟨55987503229799493508129697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37325002153199662338753131 55987503229799493508129697)
          ·
            refine ⟨41990627422349620131097273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55987503229799493508129697 41990627422349620131097273)
            ·
              refine ⟨31492970566762215098322955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41990627422349620131097273 31492970566762215098322955)
              ·
                refine ⟨47239455850143322647484433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31492970566762215098322955 47239455850143322647484433)
                ·
                  refine ⟨35429591887607491985613325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47239455850143322647484433 35429591887607491985613325)
                  ·
                    refine ⟨13286096957852809494604997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35429591887607491985613325 13286096957852809494604997)
                    ·
                      refine ⟨2491143179597401780238437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13286096957852809494604997 2491143179597401780238437)
                      ·
                        rfl

theorem cell23_4851484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_4851484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851484 prefixEnd_4851484 := by exact prefixLift 4851484
  have htrace : WordTrace (prefixWord ++ tailWord_4851484) baseStart_4851484 baseEnd_4851484 := by
    simpa [prefixWord, tailWord_4851484, baseEnd_4851484] using wordTrace_append hprefix tailTrace_4851484
  have hstable : (prefixWord ++ tailWord_4851484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851484).length < 2 ^ (prefixWord ++ tailWord_4851484).sum := by decide
  have hdescent : baseEnd_4851484 < baseStart_4851484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851505 : List Nat := [1, 2, 2, 3, 2, 4, 1, 2, 1, 3, 2]
def baseStart_4851505 : Nat := 118140960795 + 4851505 * 2 ^ 59
def prefixEnd_4851505 : Nat := 4983230072969 + 3 ^ 40 * 4851505 * 2
def baseEnd_4851505 : Nat := 2491153962691146198075841

theorem tailTrace_4851505 : CollatzResearch.WordTrace tailWord_4851505 prefixEnd_4851505 2491153962691146198075841 := by
  unfold tailWord_4851505
  simp only [CollatzResearch.WordTrace]
  refine ⟨176948924288833430933195969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117965949525888953955463979 176948924288833430933195969)
  ·
    refine ⟨132711693216625073199896977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176948924288833430933195969 132711693216625073199896977)
    ·
      refine ⟨99533769912468804899922733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132711693216625073199896977 99533769912468804899922733)
      ·
        refine ⟨37325163717175801837471025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99533769912468804899922733 37325163717175801837471025)
        ·
          refine ⟨27993872787881851378103269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37325163717175801837471025 27993872787881851378103269)
          ·
            refine ⟨5248851147727847133394363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27993872787881851378103269 5248851147727847133394363)
            ·
              refine ⟨7873276721591770700091545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5248851147727847133394363 7873276721591770700091545)
              ·
                refine ⟨5904957541193828025068659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7873276721591770700091545 5904957541193828025068659)
                ·
                  refine ⟨8857436311790742037602989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5904957541193828025068659 8857436311790742037602989)
                  ·
                    refine ⟨3321538616921528264101121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8857436311790742037602989 3321538616921528264101121)
                    ·
                      refine ⟨2491153962691146198075841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321538616921528264101121 2491153962691146198075841)
                      ·
                        rfl

theorem cell23_4851505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_4851505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851505 prefixEnd_4851505 := by exact prefixLift 4851505
  have htrace : WordTrace (prefixWord ++ tailWord_4851505) baseStart_4851505 baseEnd_4851505 := by
    simpa [prefixWord, tailWord_4851505, baseEnd_4851505] using wordTrace_append hprefix tailTrace_4851505
  have hstable : (prefixWord ++ tailWord_4851505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851505).length < 2 ^ (prefixWord ++ tailWord_4851505).sum := by decide
  have hdescent : baseEnd_4851505 < baseStart_4851505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851518 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_4851518 : Nat := 118140960795 + 4851518 * 2 ^ 59
def prefixEnd_4851518 : Nat := 4983230072969 + 3 ^ 40 * 4851518 * 2
def baseEnd_4851518 : Nat := 2491160637939654647213281

theorem tailTrace_4851518 : CollatzResearch.WordTrace tailWord_4851518 prefixEnd_4851518 2491160637939654647213281 := by
  unfold tailWord_4851518
  simp only [CollatzResearch.WordTrace]
  refine ⟨22118674804723291769177401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117966265625190889435612805 22118674804723291769177401)
  ·
    refine ⟨16589006103542468826883051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22118674804723291769177401 16589006103542468826883051)
    ·
      refine ⟨24883509155313703240324577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16589006103542468826883051 24883509155313703240324577)
      ·
        refine ⟨18662631866485277430243433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24883509155313703240324577 18662631866485277430243433)
        ·
          refine ⟨13996973899863958072682575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18662631866485277430243433 13996973899863958072682575)
          ·
            refine ⟨20995460849795937109023863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13996973899863958072682575 20995460849795937109023863)
            ·
              refine ⟨31493191274693905663535795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20995460849795937109023863 31493191274693905663535795)
              ·
                refine ⟨47239786912040858495303693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31493191274693905663535795 47239786912040858495303693)
                ·
                  refine ⟨17714920092015321935738885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47239786912040858495303693 17714920092015321935738885)
                  ·
                    refine ⟨3321547517252872862951041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17714920092015321935738885 3321547517252872862951041)
                    ·
                      refine ⟨2491160637939654647213281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321547517252872862951041 2491160637939654647213281)
                      ·
                        rfl

theorem cell23_4851518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_4851518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851518 prefixEnd_4851518 := by exact prefixLift 4851518
  have htrace : WordTrace (prefixWord ++ tailWord_4851518) baseStart_4851518 baseEnd_4851518 := by
    simpa [prefixWord, tailWord_4851518, baseEnd_4851518] using wordTrace_append hprefix tailTrace_4851518
  have hstable : (prefixWord ++ tailWord_4851518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851518).length < 2 ^ (prefixWord ++ tailWord_4851518).sum := by decide
  have hdescent : baseEnd_4851518 < baseStart_4851518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851548 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_4851548 : Nat := 118140960795 + 4851548 * 2 ^ 59
def prefixEnd_4851548 : Nat := 4983230072969 + 3 ^ 40 * 4851548 * 2
def baseEnd_4851548 : Nat := 2491176042359289529838143

theorem tailTrace_4851548 : CollatzResearch.WordTrace tailWord_4851548 prefixEnd_4851548 2491176042359289529838143 := by
  unfold tailWord_4851548
  simp only [CollatzResearch.WordTrace]
  refine ⟨88475246313838824638505649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117966995085118432851340865 88475246313838824638505649)
  ·
    refine ⟨66356434735379118478879237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88475246313838824638505649 66356434735379118478879237)
    ·
      refine ⟨12441831512883584714789857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66356434735379118478879237 12441831512883584714789857)
      ·
        refine ⟨9331373634662688536092393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12441831512883584714789857 9331373634662688536092393)
        ·
          refine ⟨6998530225997016402069295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9331373634662688536092393 6998530225997016402069295)
          ·
            refine ⟨10497795338995524603103943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6998530225997016402069295 10497795338995524603103943)
            ·
              refine ⟨15746693008493286904655915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10497795338995524603103943 15746693008493286904655915)
              ·
                refine ⟨23620039512739930356983873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15746693008493286904655915 23620039512739930356983873)
                ·
                  refine ⟨17715029634554947767737905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23620039512739930356983873 17715029634554947767737905)
                  ·
                    refine ⟨13286272225916210825803429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17715029634554947767737905 13286272225916210825803429)
                    ·
                      refine ⟨2491176042359289529838143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13286272225916210825803429 2491176042359289529838143)
                      ·
                        rfl

theorem cell23_4851548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_4851548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851548 prefixEnd_4851548 := by exact prefixLift 4851548
  have htrace : WordTrace (prefixWord ++ tailWord_4851548) baseStart_4851548 baseEnd_4851548 := by
    simpa [prefixWord, tailWord_4851548, baseEnd_4851548] using wordTrace_append hprefix tailTrace_4851548
  have hstable : (prefixWord ++ tailWord_4851548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851548).length < 2 ^ (prefixWord ++ tailWord_4851548).sum := by decide
  have hdescent : baseEnd_4851548 < baseStart_4851548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851551 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 3]
def baseStart_4851551 : Nat := 118140960795 + 4851551 * 2 ^ 59
def prefixEnd_4851551 : Nat := 4983230072969 + 3 ^ 40 * 4851551 * 2
def baseEnd_4851551 : Nat := 2491177582801253018100629

theorem tailTrace_4851551 : CollatzResearch.WordTrace tailWord_4851551 prefixEnd_4851551 2491177582801253018100629 := by
  unfold tailWord_4851551
  simp only [CollatzResearch.WordTrace]
  refine ⟨176950602046666780789370507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117967068031111187192913671 176950602046666780789370507)
  ·
    refine ⟨265425903070000171184055761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176950602046666780789370507 265425903070000171184055761)
    ·
      refine ⟨199069427302500128388041821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265425903070000171184055761 199069427302500128388041821)
      ·
        refine ⟨74651035238437548145515683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199069427302500128388041821 74651035238437548145515683)
        ·
          refine ⟨111976552857656322218273525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74651035238437548145515683 111976552857656322218273525)
          ·
            refine ⟨10497801830405280207963143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111976552857656322218273525 10497801830405280207963143)
            ·
              refine ⟨15746702745607920311944715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10497801830405280207963143 15746702745607920311944715)
              ·
                refine ⟨23620054118411880467917073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15746702745607920311944715 23620054118411880467917073)
                ·
                  refine ⟨17715040588808910350937805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23620054118411880467917073 17715040588808910350937805)
                  ·
                    refine ⟨6643140220803341381601677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17715040588808910350937805 6643140220803341381601677)
                    ·
                      refine ⟨2491177582801253018100629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6643140220803341381601677 2491177582801253018100629)
                      ·
                        rfl

theorem cell23_4851551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_4851551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851551 prefixEnd_4851551 := by exact prefixLift 4851551
  have htrace : WordTrace (prefixWord ++ tailWord_4851551) baseStart_4851551 baseEnd_4851551 := by
    simpa [prefixWord, tailWord_4851551, baseEnd_4851551] using wordTrace_append hprefix tailTrace_4851551
  have hstable : (prefixWord ++ tailWord_4851551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851551).length < 2 ^ (prefixWord ++ tailWord_4851551).sum := by decide
  have hdescent : baseEnd_4851551 < baseStart_4851551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851601 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 3, 4]
def baseStart_4851601 : Nat := 118140960795 + 4851601 * 2 ^ 59
def prefixEnd_4851601 : Nat := 4983230072969 + 3 ^ 40 * 4851601 * 2
def baseEnd_4851601 : Nat := 830401085611325940825133

theorem tailTrace_4851601 : CollatzResearch.WordTrace tailWord_4851601 prefixEnd_4851601 830401085611325940825133 := by
  unfold tailWord_4851601
  simp only [CollatzResearch.WordTrace]
  refine ⟨176952425696485639328690657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117968283797657092885793771 176952425696485639328690657)
  ·
    refine ⟨132714319272364229496517993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176952425696485639328690657 132714319272364229496517993)
    ·
      refine ⟨99535739454273172122388495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132714319272364229496517993 99535739454273172122388495)
      ·
        refine ⟨149303609181409758183582743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99535739454273172122388495 149303609181409758183582743)
        ·
          refine ⟨223955413772114637275374115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149303609181409758183582743 223955413772114637275374115)
          ·
            refine ⟨335933120658171955913061173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223955413772114637275374115 335933120658171955913061173)
            ·
              refine ⟨31493730061703620866849485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 335933120658171955913061173 31493730061703620866849485)
              ·
                refine ⟨11810148773138857825068557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31493730061703620866849485 11810148773138857825068557)
                ·
                  refine ⟨4428805789927071684400709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11810148773138857825068557 4428805789927071684400709)
                  ·
                    refine ⟨830401085611325940825133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4428805789927071684400709 830401085611325940825133)
                    ·
                      rfl

theorem cell23_4851601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_4851601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851601 prefixEnd_4851601 := by exact prefixLift 4851601
  have htrace : WordTrace (prefixWord ++ tailWord_4851601) baseStart_4851601 baseEnd_4851601 := by
    simpa [prefixWord, tailWord_4851601, baseEnd_4851601] using wordTrace_append hprefix tailTrace_4851601
  have hstable : (prefixWord ++ tailWord_4851601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851601).length < 2 ^ (prefixWord ++ tailWord_4851601).sum := by decide
  have hdescent : baseEnd_4851601 < baseStart_4851601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851691 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 6, 4]
def baseStart_4851691 : Nat := 118140960795 + 4851691 * 2 ^ 59
def prefixEnd_4851691 : Nat := 4983230072969 + 3 ^ 40 * 4851691 * 2
def baseEnd_4851691 : Nat := 830416490030960823449995

theorem tailTrace_4851691 : CollatzResearch.WordTrace tailWord_4851691 prefixEnd_4851691 830416490030960823449995 := by
  unfold tailWord_4851691
  simp only [CollatzResearch.WordTrace]
  refine ⟨176955708266159584699466927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117970472177439723132977951 176955708266159584699466927)
  ·
    refine ⟨265433562399239377049200391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176955708266159584699466927 265433562399239377049200391)
    ·
      refine ⟨398150343598859065573800587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265433562399239377049200391 398150343598859065573800587)
      ·
        refine ⟨597225515398288598360700881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398150343598859065573800587 597225515398288598360700881)
        ·
          refine ⟨447919136548716448770525661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597225515398288598360700881 447919136548716448770525661)
          ·
            refine ⟨167969676205768668288947123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 447919136548716448770525661 167969676205768668288947123)
            ·
              refine ⟨251954514308653002433420685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167969676205768668288947123 251954514308653002433420685)
              ·
                refine ⟨94482942865744875912532757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251954514308653002433420685 94482942865744875912532757)
                ·
                  refine ⟨4428887946831791058399973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94482942865744875912532757 4428887946831791058399973)
                  ·
                    refine ⟨830416490030960823449995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4428887946831791058399973 830416490030960823449995)
                    ·
                      rfl

theorem cell23_4851691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 4].length) (baseStart_4851691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851691 prefixEnd_4851691 := by exact prefixLift 4851691
  have htrace : WordTrace (prefixWord ++ tailWord_4851691) baseStart_4851691 baseEnd_4851691 := by
    simpa [prefixWord, tailWord_4851691, baseEnd_4851691] using wordTrace_append hprefix tailTrace_4851691
  have hstable : (prefixWord ++ tailWord_4851691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851691).length < 2 ^ (prefixWord ++ tailWord_4851691).sum := by decide
  have hdescent : baseEnd_4851691 < baseStart_4851691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851738 : List Nat := [3, 1, 1, 3, 1, 4, 3, 7]
def baseStart_4851738 : Nat := 118140960795 + 4851738 * 2 ^ 59
def prefixEnd_4851738 : Nat := 4983230072969 + 3 ^ 40 * 4851738 * 2
def baseEnd_4851738 : Nat := 92269392729023843943047

theorem tailTrace_4851738 : CollatzResearch.WordTrace tailWord_4851738 prefixEnd_4851738 92269392729023843943047 := by
  unfold tailWord_4851738
  simp only [CollatzResearch.WordTrace]
  refine ⟨44239355624247327931606967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117971614997992874484285245 44239355624247327931606967)
  ·
    refine ⟨66359033436370991897410451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44239355624247327931606967 66359033436370991897410451)
    ·
      refine ⟨99538550154556487846115677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66359033436370991897410451 99538550154556487846115677)
      ·
        refine ⟨37326956307958682942293379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99538550154556487846115677 37326956307958682942293379)
        ·
          refine ⟨55990434461938024413440069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37326956307958682942293379 55990434461938024413440069)
          ·
            refine ⟨10498206461613379577520013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55990434461938024413440069 10498206461613379577520013)
            ·
              refine ⟨3936827423105017341570005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10498206461613379577520013 3936827423105017341570005)
              ·
                refine ⟨92269392729023843943047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3936827423105017341570005 92269392729023843943047)
                ·
                  rfl

theorem cell23_4851738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 7].length) (baseStart_4851738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851738 prefixEnd_4851738 := by exact prefixLift 4851738
  have htrace : WordTrace (prefixWord ++ tailWord_4851738) baseStart_4851738 baseEnd_4851738 := by
    simpa [prefixWord, tailWord_4851738, baseEnd_4851738] using wordTrace_append hprefix tailTrace_4851738
  have hstable : (prefixWord ++ tailWord_4851738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851738).length < 2 ^ (prefixWord ++ tailWord_4851738).sum := by decide
  have hdescent : baseEnd_4851738 < baseStart_4851738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851749 : List Nat := [1, 3, 1, 2, 2, 4, 2, 3, 1, 2, 2]
def baseStart_4851749 : Nat := 118140960795 + 4851749 * 2 ^ 59
def prefixEnd_4851749 : Nat := 4983230072969 + 3 ^ 40 * 4851749 * 2
def baseEnd_4851749 : Nat := 2491279251970843243424719

theorem tailTrace_4851749 : CollatzResearch.WordTrace tailWord_4851749 prefixEnd_4851749 2491279251970843243424719 := by
  unfold tailWord_4851749
  simp only [CollatzResearch.WordTrace]
  refine ⟨176957823699949460605078301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117971882466632973736718867 176957823699949460605078301)
  ·
    refine ⟨66359183887481047726904363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176957823699949460605078301 66359183887481047726904363)
    ·
      refine ⟨99538775831221571590356545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66359183887481047726904363 99538775831221571590356545)
      ·
        refine ⟨74654081873416178692767409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99538775831221571590356545 74654081873416178692767409)
        ·
          refine ⟨55990561405062134019575557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74654081873416178692767409 55990561405062134019575557)
          ·
            refine ⟨10498230263449150128670417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55990561405062134019575557 10498230263449150128670417)
            ·
              refine ⟨7873672697586862596502813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10498230263449150128670417 7873672697586862596502813)
              ·
                refine ⟨2952627261595073473688555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7873672697586862596502813 2952627261595073473688555)
                ·
                  refine ⟨4428940892392610210532833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2952627261595073473688555 4428940892392610210532833)
                  ·
                    refine ⟨3321705669294457657899625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4428940892392610210532833 3321705669294457657899625)
                    ·
                      refine ⟨2491279251970843243424719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321705669294457657899625 2491279251970843243424719)
                      ·
                        rfl

theorem cell23_4851749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_4851749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851749 prefixEnd_4851749 := by exact prefixLift 4851749
  have htrace : WordTrace (prefixWord ++ tailWord_4851749) baseStart_4851749 baseEnd_4851749 := by
    simpa [prefixWord, tailWord_4851749, baseEnd_4851749] using wordTrace_append hprefix tailTrace_4851749
  have hstable : (prefixWord ++ tailWord_4851749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851749).length < 2 ^ (prefixWord ++ tailWord_4851749).sum := by decide
  have hdescent : baseEnd_4851749 < baseStart_4851749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851791 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 5]
def baseStart_4851791 : Nat := 118140960795 + 4851791 * 2 ^ 59
def prefixEnd_4851791 : Nat := 4983230072969 + 3 ^ 40 * 4851791 * 2
def baseEnd_4851791 : Nat := 2491300818158332079099525

theorem tailTrace_4851791 : CollatzResearch.WordTrace tailWord_4851791 prefixEnd_4851791 2491300818158332079099525 := by
  unfold tailWord_4851791
  simp only [CollatzResearch.WordTrace]
  refine ⟨176959355565797301778107227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117972903710531534518738151 176959355565797301778107227)
  ·
    refine ⟨265439033348695952667160841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176959355565797301778107227 265439033348695952667160841)
    ·
      refine ⟨199079275011521964500370631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265439033348695952667160841 199079275011521964500370631)
      ·
        refine ⟨298618912517282946750555947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199079275011521964500370631 298618912517282946750555947)
        ·
          refine ⟨447928368775924420125833921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298618912517282946750555947 447928368775924420125833921)
          ·
            refine ⟨335946276581943315094375441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447928368775924420125833921 335946276581943315094375441)
            ·
              refine ⟨251959707436457486320781581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335946276581943315094375441 251959707436457486320781581)
              ·
                refine ⟨94484890288671557370293093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251959707436457486320781581 94484890288671557370293093)
                ·
                  refine ⟨17715916929125917006929955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94484890288671557370293093 17715916929125917006929955)
                  ·
                    refine ⟨26573875393688875510394933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17715916929125917006929955 26573875393688875510394933)
                    ·
                      refine ⟨2491300818158332079099525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26573875393688875510394933 2491300818158332079099525)
                      ·
                        rfl

theorem cell23_4851791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_4851791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851791 prefixEnd_4851791 := by exact prefixLift 4851791
  have htrace : WordTrace (prefixWord ++ tailWord_4851791) baseStart_4851791 baseEnd_4851791 := by
    simpa [prefixWord, tailWord_4851791, baseEnd_4851791] using wordTrace_append hprefix tailTrace_4851791
  have hstable : (prefixWord ++ tailWord_4851791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851791).length < 2 ^ (prefixWord ++ tailWord_4851791).sum := by decide
  have hdescent : baseEnd_4851791 < baseStart_4851791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851808 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 5]
def baseStart_4851808 : Nat := 118140960795 + 4851808 * 2 ^ 59
def prefixEnd_4851808 : Nat := 4983230072969 + 3 ^ 40 * 4851808 * 2
def baseEnd_4851808 : Nat := 2491309547329458512586947

theorem tailTrace_4851808 : CollatzResearch.WordTrace tailWord_4851808 prefixEnd_4851808 2491309547329458512586947 := by
  unfold tailWord_4851808
  simp only [CollatzResearch.WordTrace]
  refine ⟨88479987803367856840738039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117973317071157142454317385 88479987803367856840738039)
  ·
    refine ⟨132719981705051785261107059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88479987803367856840738039 132719981705051785261107059)
    ·
      refine ⟨199079972557577677891660589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132719981705051785261107059 199079972557577677891660589)
      ·
        refine ⟨74654989709091629209372721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199079972557577677891660589 74654989709091629209372721)
        ·
          refine ⟨55991242281818721907029541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74654989709091629209372721 55991242281818721907029541)
          ·
            refine ⟨10498357927841010357568039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55991242281818721907029541 10498357927841010357568039)
            ·
              refine ⟨15747536891761515536352059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10498357927841010357568039 15747536891761515536352059)
              ·
                refine ⟨23621305337642273304528089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15747536891761515536352059 23621305337642273304528089)
                ·
                  refine ⟨17715979003231704978396067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23621305337642273304528089 17715979003231704978396067)
                  ·
                    refine ⟨26573968504847557467594101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17715979003231704978396067 26573968504847557467594101)
                    ·
                      refine ⟨2491309547329458512586947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26573968504847557467594101 2491309547329458512586947)
                      ·
                        rfl

theorem cell23_4851808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_4851808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851808 prefixEnd_4851808 := by exact prefixLift 4851808
  have htrace : WordTrace (prefixWord ++ tailWord_4851808) baseStart_4851808 baseEnd_4851808 := by
    simpa [prefixWord, tailWord_4851808, baseEnd_4851808] using wordTrace_append hprefix tailTrace_4851808
  have hstable : (prefixWord ++ tailWord_4851808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851808).length < 2 ^ (prefixWord ++ tailWord_4851808).sum := by decide
  have hdescent : baseEnd_4851808 < baseStart_4851808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851811 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 9]
def baseStart_4851811 : Nat := 118140960795 + 4851811 * 2 ^ 59
def prefixEnd_4851811 : Nat := 4983230072969 + 3 ^ 40 * 4851811 * 2
def baseEnd_4851811 : Nat := 276812343085713555649937

theorem tailTrace_4851811 : CollatzResearch.WordTrace tailWord_4851811 prefixEnd_4851811 276812343085713555649937 := by
  unfold tailWord_4851811
  simp only [CollatzResearch.WordTrace]
  refine ⟨176960085025724845193835287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117973390017149896795890191 176960085025724845193835287)
  ·
    refine ⟨265440127538587267790752931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176960085025724845193835287 265440127538587267790752931)
    ·
      refine ⟨398160191307880901686129397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265440127538587267790752931 398160191307880901686129397)
      ·
        refine ⟨37327517935113834533074631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 398160191307880901686129397 37327517935113834533074631)
        ·
          refine ⟨55991276902670751799611947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37327517935113834533074631 55991276902670751799611947)
          ·
            refine ⟨83986915354006127699417921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55991276902670751799611947 83986915354006127699417921)
            ·
              refine ⟨62990186515504595774563441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83986915354006127699417921 62990186515504595774563441)
              ·
                refine ⟨47242639886628446830922581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62990186515504595774563441 47242639886628446830922581)
                ·
                  refine ⟨276812343085713555649937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47242639886628446830922581 276812343085713555649937)
                  ·
                    rfl

theorem cell23_4851811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 9].length) (baseStart_4851811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851811 prefixEnd_4851811 := by exact prefixLift 4851811
  have htrace : WordTrace (prefixWord ++ tailWord_4851811) baseStart_4851811 baseEnd_4851811 := by
    simpa [prefixWord, tailWord_4851811, baseEnd_4851811] using wordTrace_append hprefix tailTrace_4851811
  have hstable : (prefixWord ++ tailWord_4851811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851811).length < 2 ^ (prefixWord ++ tailWord_4851811).sum := by decide
  have hdescent : baseEnd_4851811 < baseStart_4851811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851822 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_4851822 : Nat := 118140960795 + 4851822 * 2 ^ 59
def prefixEnd_4851822 : Nat := 4983230072969 + 3 ^ 40 * 4851822 * 2
def baseEnd_4851822 : Nat := 2491316736058621457811883

theorem tailTrace_4851822 : CollatzResearch.WordTrace tailWord_4851822 prefixEnd_4851822 2491316736058621457811883 := by
  unfold tailWord_4851822
  simp only [CollatzResearch.WordTrace]
  refine ⟨22120060778585624259060715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117973657485789996048323813 22120060778585624259060715)
  ·
    refine ⟨33180091167878436388591073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22120060778585624259060715 33180091167878436388591073)
    ·
      refine ⟨24885068375908827291443305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33180091167878436388591073 24885068375908827291443305)
      ·
        refine ⟨18663801281931620468582479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24885068375908827291443305 18663801281931620468582479)
        ·
          refine ⟨27995701922897430702873719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18663801281931620468582479 27995701922897430702873719)
          ·
            refine ⟨41993552884346146054310579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27995701922897430702873719 41993552884346146054310579)
            ·
              refine ⟨62990329326519219081465869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41993552884346146054310579 62990329326519219081465869)
              ·
                refine ⟨23621373497444707155549701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62990329326519219081465869 23621373497444707155549701)
                ·
                  refine ⟨4429007530770882591665569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23621373497444707155549701 4429007530770882591665569)
                  ·
                    refine ⟨3321755648078161943749177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4429007530770882591665569 3321755648078161943749177)
                    ·
                      refine ⟨2491316736058621457811883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3321755648078161943749177 2491316736058621457811883)
                      ·
                        rfl

theorem cell23_4851822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_4851822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851822 prefixEnd_4851822 := by exact prefixLift 4851822
  have htrace : WordTrace (prefixWord ++ tailWord_4851822) baseStart_4851822 baseEnd_4851822 := by
    simpa [prefixWord, tailWord_4851822, baseEnd_4851822] using wordTrace_append hprefix tailTrace_4851822
  have hstable : (prefixWord ++ tailWord_4851822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851822).length < 2 ^ (prefixWord ++ tailWord_4851822).sum := by decide
  have hdescent : baseEnd_4851822 < baseStart_4851822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851868 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_4851868 : Nat := 118140960795 + 4851868 * 2 ^ 59
def prefixEnd_4851868 : Nat := 4983230072969 + 3 ^ 40 * 4851868 * 2
def baseEnd_4851868 : Nat := 2491340356168728277836671

theorem tailTrace_4851868 : CollatzResearch.WordTrace tailWord_4851868 prefixEnd_4851868 2491340356168728277836671 := by
  unfold tailWord_4851868
  simp only [CollatzResearch.WordTrace]
  refine ⟨88481081993259171964330129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117974775991012229285773505 88481081993259171964330129)
  ·
    refine ⟨66360811494944378973247597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88481081993259171964330129 66360811494944378973247597)
    ·
      refine ⟨24885304310604142114967849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66360811494944378973247597 24885304310604142114967849)
      ·
        refine ⟨18663978232953106586225887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24885304310604142114967849 18663978232953106586225887)
        ·
          refine ⟨27995967349429659879338831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18663978232953106586225887 27995967349429659879338831)
          ·
            refine ⟨41993951024144489819008247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27995967349429659879338831 41993951024144489819008247)
            ·
              refine ⟨62990926536216734728512371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41993951024144489819008247 62990926536216734728512371)
              ·
                refine ⟨94486389804325102092768557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62990926536216734728512371 94486389804325102092768557)
                ·
                  refine ⟨35432396176621913284788209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94486389804325102092768557 35432396176621913284788209)
                  ·
                    refine ⟨26574297132466434963591157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35432396176621913284788209 26574297132466434963591157)
                    ·
                      refine ⟨2491340356168728277836671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26574297132466434963591157 2491340356168728277836671)
                      ·
                        rfl

theorem cell23_4851868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_4851868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851868 prefixEnd_4851868 := by exact prefixLift 4851868
  have htrace : WordTrace (prefixWord ++ tailWord_4851868) baseStart_4851868 baseEnd_4851868 := by
    simpa [prefixWord, tailWord_4851868, baseEnd_4851868] using wordTrace_append hprefix tailTrace_4851868
  have hstable : (prefixWord ++ tailWord_4851868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851868).length < 2 ^ (prefixWord ++ tailWord_4851868).sum := by decide
  have hdescent : baseEnd_4851868 < baseStart_4851868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4851885 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_4851885 : Nat := 118140960795 + 4851885 * 2 ^ 59
def prefixEnd_4851885 : Nat := 4983230072969 + 3 ^ 40 * 4851885 * 2
def baseEnd_4851885 : Nat := 2491349085339854711324093

theorem tailTrace_4851885 : CollatzResearch.WordTrace tailWord_4851885 prefixEnd_4851885 2491349085339854711324093 := by
  unfold tailWord_4851885
  simp only [CollatzResearch.WordTrace]
  refine ⟨176962784027456755832029109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117975189351637837221352739 176962784027456755832029109)
  ·
    refine ⟨16590261002574070859252729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176962784027456755832029109 16590261002574070859252729)
    ·
      refine ⟨12442695751930553144439547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16590261002574070859252729 12442695751930553144439547)
      ·
        refine ⟨18664043627895829716659321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12442695751930553144439547 18664043627895829716659321)
        ·
          refine ⟨13998032720921872287494491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18664043627895829716659321 13998032720921872287494491)
          ·
            refine ⟨20997049081382808431241737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13998032720921872287494491 20997049081382808431241737)
            ·
              refine ⟨15747786811037106323431303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20997049081382808431241737 15747786811037106323431303)
              ·
                refine ⟨23621680216555659485146955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15747786811037106323431303 23621680216555659485146955)
                ·
                  refine ⟨35432520324833489227720433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23621680216555659485146955 35432520324833489227720433)
                  ·
                    refine ⟨26574390243625116920790325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35432520324833489227720433 26574390243625116920790325)
                    ·
                      refine ⟨2491349085339854711324093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26574390243625116920790325 2491349085339854711324093)
                      ·
                        rfl

theorem cell23_4851885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_4851885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4851885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4851885 prefixEnd_4851885 := by exact prefixLift 4851885
  have htrace : WordTrace (prefixWord ++ tailWord_4851885) baseStart_4851885 baseEnd_4851885 := by
    simpa [prefixWord, tailWord_4851885, baseEnd_4851885] using wordTrace_append hprefix tailTrace_4851885
  have hstable : (prefixWord ++ tailWord_4851885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4851885).length < 2 ^ (prefixWord ++ tailWord_4851885).sum := by decide
  have hdescent : baseEnd_4851885 < baseStart_4851885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4851885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
