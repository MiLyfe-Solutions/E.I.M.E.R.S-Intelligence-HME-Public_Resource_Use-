import V185TrunkScan22Chunk011

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_105740 : List Nat := [2, 2, 1, 2, 2, 3, 3, 2, 5]
def baseStart_105740 : Nat := 118140960795 + 105740 * 2 ^ 59
def prefixEnd_105740 : Nat := 4983230072969 + 3 ^ 40 * 105740 * 2
def baseEnd_105740 : Nat := 12065654312560338991937

theorem tailTrace_105740 : CollatzResearch.WordTrace tailWord_105740 prefixEnd_105740 12065654312560338991937 := by
  unfold tailWord_105740
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928327318464756899681337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2571103091286342532908449 1928327318464756899681337)
  ·
    refine ⟨1446245488848567674761003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1928327318464756899681337 1446245488848567674761003)
    ·
      refine ⟨2169368233272851512141505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1446245488848567674761003 2169368233272851512141505)
      ·
        refine ⟨1627026174954638634106129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2169368233272851512141505 1627026174954638634106129)
        ·
          refine ⟨1220269631215978975579597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1627026174954638634106129 1220269631215978975579597)
          ·
            refine ⟨457601111705992115842349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1220269631215978975579597 457601111705992115842349)
            ·
              refine ⟨171600416889747043440881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 457601111705992115842349 171600416889747043440881)
              ·
                refine ⟨128700312667310282580661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171600416889747043440881 128700312667310282580661)
                ·
                  refine ⟨12065654312560338991937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128700312667310282580661 12065654312560338991937)
                  ·
                    rfl

theorem cell22_105740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_105740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105740 prefixEnd_105740 := by exact prefixLift 105740
  have htrace : WordTrace (prefixWord ++ tailWord_105740) baseStart_105740 baseEnd_105740 := by
    simpa [prefixWord, tailWord_105740, baseEnd_105740] using wordTrace_append hprefix tailTrace_105740
  have hstable : (prefixWord ++ tailWord_105740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105740).length < 2 ^ (prefixWord ++ tailWord_105740).sum := by decide
  have hdescent : baseEnd_105740 < baseStart_105740 := by decide
  rcases family_descends (prefixWord ++ tailWord_105740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105821 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_105821 : Nat := 118140960795 + 105821 * 2 ^ 59
def prefixEnd_105821 : Nat := 4983230072969 + 3 ^ 40 * 105821 * 2
def baseEnd_105821 : Nat := 36224690893023805700563

theorem tailTrace_105821 : CollatzResearch.WordTrace tailWord_105821 prefixEnd_105821 36224690893023805700563 := by
  unfold tailWord_105821
  simp only [CollatzResearch.WordTrace]
  refine ⟨3859608949636064633061317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2573072633090709755374211 3859608949636064633061317)
  ·
    refine ⟨723676678056762118698997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3859608949636064633061317 723676678056762118698997)
    ·
      refine ⟨67844688567821448628031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 723676678056762118698997 67844688567821448628031)
      ·
        refine ⟨101767032851732172942047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67844688567821448628031 101767032851732172942047)
        ·
          refine ⟨152650549277598259413071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101767032851732172942047 152650549277598259413071)
          ·
            refine ⟨228975823916397389119607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152650549277598259413071 228975823916397389119607)
            ·
              refine ⟨343463735874596083679411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228975823916397389119607 343463735874596083679411)
              ·
                refine ⟨515195603811894125519117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343463735874596083679411 515195603811894125519117)
                ·
                  refine ⟨193198351429460297069669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515195603811894125519117 193198351429460297069669)
                  ·
                    refine ⟨36224690893023805700563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 193198351429460297069669 36224690893023805700563)
                    ·
                      rfl

theorem cell22_105821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_105821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105821 prefixEnd_105821 := by exact prefixLift 105821
  have htrace : WordTrace (prefixWord ++ tailWord_105821) baseStart_105821 baseEnd_105821 := by
    simpa [prefixWord, tailWord_105821, baseEnd_105821] using wordTrace_append hprefix tailTrace_105821
  have hstable : (prefixWord ++ tailWord_105821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105821).length < 2 ^ (prefixWord ++ tailWord_105821).sum := by decide
  have hdescent : baseEnd_105821 < baseStart_105821 := by decide
  rcases family_descends (prefixWord ++ tailWord_105821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105843 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 3, 8]
def baseStart_105843 : Nat := 118140960795 + 105843 * 2 ^ 59
def prefixEnd_105843 : Nat := 4983230072969 + 3 ^ 40 * 105843 * 2
def baseEnd_105843 : Nat := 36232221942623081650495

theorem tailTrace_105843 : CollatzResearch.WordTrace tailWord_105843 prefixEnd_105843 36232221942623081650495 := by
  unfold tailWord_105843
  simp only [CollatzResearch.WordTrace]
  refine ⟨3860411355556362390362183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2573607570370908260241455 3860411355556362390362183)
  ·
    refine ⟨5790617033334543585543275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3860411355556362390362183 5790617033334543585543275)
    ·
      refine ⟨8685925550001815378314913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5790617033334543585543275 8685925550001815378314913)
      ·
        refine ⟨6514444162501361533736185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8685925550001815378314913 6514444162501361533736185)
        ·
          refine ⟨4885833121876021150302139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6514444162501361533736185 4885833121876021150302139)
          ·
            refine ⟨7328749682814031725453209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4885833121876021150302139 7328749682814031725453209)
            ·
              refine ⟨5496562262110523794089907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7328749682814031725453209 5496562262110523794089907)
              ·
                refine ⟨8244843393165785691134861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5496562262110523794089907 8244843393165785691134861)
                ·
                  refine ⟨3091816272437169634175573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8244843393165785691134861 3091816272437169634175573)
                  ·
                    refine ⟨36232221942623081650495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3091816272437169634175573 36232221942623081650495)
                    ·
                      rfl

theorem cell22_105843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 8].length) (baseStart_105843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105843 prefixEnd_105843 := by exact prefixLift 105843
  have htrace : WordTrace (prefixWord ++ tailWord_105843) baseStart_105843 baseEnd_105843 := by
    simpa [prefixWord, tailWord_105843, baseEnd_105843] using wordTrace_append hprefix tailTrace_105843
  have hstable : (prefixWord ++ tailWord_105843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105843).length < 2 ^ (prefixWord ++ tailWord_105843).sum := by decide
  have hdescent : baseEnd_105843 < baseStart_105843 := by decide
  rcases family_descends (prefixWord ++ tailWord_105843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105860 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_105860 : Nat := 118140960795 + 105860 * 2 ^ 59
def prefixEnd_105860 : Nat := 4983230072969 + 3 ^ 40 * 105860 * 2
def baseEnd_105860 : Nat := 36238041390040703975443

theorem tailTrace_105860 : CollatzResearch.WordTrace tailWord_105860 prefixEnd_105860 36238041390040703975443 := by
  unfold tailWord_105860
  simp only [CollatzResearch.WordTrace]
  refine ⟨1930515698247387146865517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2574020930996516195820689 1930515698247387146865517)
  ·
    refine ⟨723943386842770180074569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1930515698247387146865517 723943386842770180074569)
    ·
      refine ⟨542957540132077635055927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 723943386842770180074569 542957540132077635055927)
      ·
        refine ⟨814436310198116452583891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542957540132077635055927 814436310198116452583891)
        ·
          refine ⟨1221654465297174678875837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814436310198116452583891 1221654465297174678875837)
          ·
            refine ⟨458120424486440504578439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1221654465297174678875837 458120424486440504578439)
            ·
              refine ⟨687180636729660756867659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 458120424486440504578439 687180636729660756867659)
              ·
                refine ⟨1030770955094491135301489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 687180636729660756867659 1030770955094491135301489)
                ·
                  refine ⟨773078216320868351476117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1030770955094491135301489 773078216320868351476117)
                  ·
                    refine ⟨36238041390040703975443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 773078216320868351476117 36238041390040703975443)
                    ·
                      rfl

theorem cell22_105860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_105860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105860 prefixEnd_105860 := by exact prefixLift 105860
  have htrace : WordTrace (prefixWord ++ tailWord_105860) baseStart_105860 baseEnd_105860 := by
    simpa [prefixWord, tailWord_105860, baseEnd_105860] using wordTrace_append hprefix tailTrace_105860
  have hstable : (prefixWord ++ tailWord_105860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105860).length < 2 ^ (prefixWord ++ tailWord_105860).sum := by decide
  have hdescent : baseEnd_105860 < baseStart_105860 := by decide
  rcases family_descends (prefixWord ++ tailWord_105860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105909 : List Nat := [1, 3, 3, 2, 2, 3, 1, 2, 5]
def baseStart_105909 : Nat := 118140960795 + 105909 * 2 ^ 59
def prefixEnd_105909 : Nat := 4983230072969 + 3 ^ 40 * 105909 * 2
def baseEnd_105909 : Nat := 12084938363806969833431

theorem tailTrace_105909 : CollatzResearch.WordTrace tailWord_105909 prefixEnd_105909 12084938363806969833431 := by
  unfold tailWord_105909
  simp only [CollatzResearch.WordTrace]
  refine ⟨3862818573317255662264781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2575212382211503774843187 3862818573317255662264781)
  ·
    refine ⟨1448556964993970873349293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3862818573317255662264781 1448556964993970873349293)
    ·
      refine ⟨543208861872739077505985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1448556964993970873349293 543208861872739077505985)
      ·
        refine ⟨407406646404554308129489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543208861872739077505985 407406646404554308129489)
        ·
          refine ⟨305554984803415731097117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407406646404554308129489 305554984803415731097117)
          ·
            refine ⟨114583119301280899161419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305554984803415731097117 114583119301280899161419)
            ·
              refine ⟨171874678951921348742129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114583119301280899161419 171874678951921348742129)
              ·
                refine ⟨128906009213941011556597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171874678951921348742129 128906009213941011556597)
                ·
                  refine ⟨12084938363806969833431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128906009213941011556597 12084938363806969833431)
                  ·
                    rfl

theorem cell22_105909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_105909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105909 prefixEnd_105909 := by exact prefixLift 105909
  have htrace : WordTrace (prefixWord ++ tailWord_105909) baseStart_105909 baseEnd_105909 := by
    simpa [prefixWord, tailWord_105909, baseEnd_105909] using wordTrace_append hprefix tailTrace_105909
  have hstable : (prefixWord ++ tailWord_105909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105909).length < 2 ^ (prefixWord ++ tailWord_105909).sum := by decide
  have hdescent : baseEnd_105909 < baseStart_105909 := by decide
  rcases family_descends (prefixWord ++ tailWord_105909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105920 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 6]
def baseStart_105920 : Nat := 118140960795 + 105920 * 2 ^ 59
def prefixEnd_105920 : Nat := 4983230072969 + 3 ^ 40 * 105920 * 2
def baseEnd_105920 : Nat := 12086193538740182491753

theorem tailTrace_105920 : CollatzResearch.WordTrace tailWord_105920 prefixEnd_105920 12086193538740182491753 := by
  unfold tailWord_105920
  simp only [CollatzResearch.WordTrace]
  refine ⟨1931609888138702270457607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2575479850851603027276809 1931609888138702270457607)
  ·
    refine ⟨2897414832208053405686411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1931609888138702270457607 2897414832208053405686411)
    ·
      refine ⟨4346122248312080108529617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2897414832208053405686411 4346122248312080108529617)
      ·
        refine ⟨3259591686234060081397213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4346122248312080108529617 3259591686234060081397213)
        ·
          refine ⟨1222346882337772530523955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3259591686234060081397213 1222346882337772530523955)
          ·
            refine ⟨1833520323506658795785933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1222346882337772530523955 1833520323506658795785933)
            ·
              refine ⟨687570121314997048419725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1833520323506658795785933 687570121314997048419725)
              ·
                refine ⟨257838795493123893157397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 687570121314997048419725 257838795493123893157397)
                ·
                  refine ⟨12086193538740182491753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 257838795493123893157397 12086193538740182491753)
                  ·
                    rfl

theorem cell22_105920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_105920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_105920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_105920 prefixEnd_105920 := by exact prefixLift 105920
  have htrace : WordTrace (prefixWord ++ tailWord_105920) baseStart_105920 baseEnd_105920 := by
    simpa [prefixWord, tailWord_105920, baseEnd_105920] using wordTrace_append hprefix tailTrace_105920
  have hstable : (prefixWord ++ tailWord_105920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105920).length < 2 ^ (prefixWord ++ tailWord_105920).sum := by decide
  have hdescent : baseEnd_105920 < baseStart_105920 := by decide
  rcases family_descends (prefixWord ++ tailWord_105920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106042 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_106042 : Nat := 118140960795 + 106042 * 2 ^ 59
def prefixEnd_106042 : Nat := 4983230072969 + 3 ^ 40 * 106042 * 2
def baseEnd_106042 : Nat := 36300343709452895924885

theorem tailTrace_106042 : CollatzResearch.WordTrace tailWord_106042 prefixEnd_106042 36300343709452895924885 := by
  unfold tailWord_106042
  simp only [CollatzResearch.WordTrace]
  refine ⟨966917370458854844214095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2578446321223612917904253 966917370458854844214095)
  ·
    refine ⟨1450376055688282266321143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 966917370458854844214095 1450376055688282266321143)
    ·
      refine ⟨2175564083532423399481715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1450376055688282266321143 2175564083532423399481715)
      ·
        refine ⟨3263346125298635099222573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2175564083532423399481715 3263346125298635099222573)
        ·
          refine ⟨1223754796986988162208465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3263346125298635099222573 1223754796986988162208465)
          ·
            refine ⟨917816097740241121656349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1223754796986988162208465 917816097740241121656349)
            ·
              refine ⟨344181036652590420621131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 917816097740241121656349 344181036652590420621131)
              ·
                refine ⟨516271554978885630931697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344181036652590420621131 516271554978885630931697)
                ·
                  refine ⟨387203666234164223198773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 516271554978885630931697 387203666234164223198773)
                  ·
                    refine ⟨36300343709452895924885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 387203666234164223198773 36300343709452895924885)
                    ·
                      rfl

theorem cell22_106042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_106042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106042 prefixEnd_106042 := by exact prefixLift 106042
  have htrace : WordTrace (prefixWord ++ tailWord_106042) baseStart_106042 baseEnd_106042 := by
    simpa [prefixWord, tailWord_106042, baseEnd_106042] using wordTrace_append hprefix tailTrace_106042
  have hstable : (prefixWord ++ tailWord_106042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106042).length < 2 ^ (prefixWord ++ tailWord_106042).sum := by decide
  have hdescent : baseEnd_106042 < baseStart_106042 := by decide
  rcases family_descends (prefixWord ++ tailWord_106042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106087 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 3, 5]
def baseStart_106087 : Nat := 118140960795 + 106087 * 2 ^ 59
def prefixEnd_106087 : Nat := 4983230072969 + 3 ^ 40 * 106087 * 2
def baseEnd_106087 : Nat := 36315748129087778549747

theorem tailTrace_106087 : CollatzResearch.WordTrace tailWord_106087 prefixEnd_106087 36315748129087778549747 := by
  unfold tailWord_106087
  simp only [CollatzResearch.WordTrace]
  refine ⟨3869310766672392062244515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2579540511114928041496343 3869310766672392062244515)
  ·
    refine ⟨5803966150008588093366773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3869310766672392062244515 5803966150008588093366773)
    ·
      refine ⟨544121826563305133753135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5803966150008588093366773 544121826563305133753135)
      ·
        refine ⟨816182739844957700629703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544121826563305133753135 816182739844957700629703)
        ·
          refine ⟨1224274109767436550944555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816182739844957700629703 1224274109767436550944555)
          ·
            refine ⟨1836411164651154826416833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224274109767436550944555 1836411164651154826416833)
            ·
              refine ⟨1377308373488366119812625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1836411164651154826416833 1377308373488366119812625)
              ·
                refine ⟨1032981280116274589859469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1377308373488366119812625 1032981280116274589859469)
                ·
                  refine ⟨387367980043602971197301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1032981280116274589859469 387367980043602971197301)
                  ·
                    refine ⟨36315748129087778549747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 387367980043602971197301 36315748129087778549747)
                    ·
                      rfl

theorem cell22_106087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_106087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106087 prefixEnd_106087 := by exact prefixLift 106087
  have htrace : WordTrace (prefixWord ++ tailWord_106087) baseStart_106087 baseEnd_106087 := by
    simpa [prefixWord, tailWord_106087, baseEnd_106087] using wordTrace_append hprefix tailTrace_106087
  have hstable : (prefixWord ++ tailWord_106087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106087).length < 2 ^ (prefixWord ++ tailWord_106087).sum := by decide
  have hdescent : baseEnd_106087 < baseStart_106087 := by decide
  rcases family_descends (prefixWord ++ tailWord_106087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106089 : List Nat := [1, 2, 1, 1, 1, 4, 4, 4, 4]
def baseStart_106089 : Nat := 118140960795 + 106089 * 2 ^ 59
def prefixEnd_106089 : Nat := 4983230072969 + 3 ^ 40 * 106089 * 2
def baseEnd_106089 : Nat := 12105477589986813333247

theorem tailTrace_106089 : CollatzResearch.WordTrace tailWord_106089 prefixEnd_106089 12105477589986813333247 := by
  unfold tailWord_106089
  simp only [CollatzResearch.WordTrace]
  refine ⟨3869383712665146403817321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2579589141776764269211547 3869383712665146403817321)
  ·
    refine ⟨2902037784498859802862991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3869383712665146403817321 2902037784498859802862991)
    ·
      refine ⟨4353056676748289704294487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2902037784498859802862991 4353056676748289704294487)
      ·
        refine ⟨6529585015122434556441731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4353056676748289704294487 6529585015122434556441731)
        ·
          refine ⟨9794377522683651834662597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6529585015122434556441731 9794377522683651834662597)
          ·
            refine ⟨1836445785503184718999237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9794377522683651834662597 1836445785503184718999237)
            ·
              refine ⟨344333584781847134812357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1836445785503184718999237 344333584781847134812357)
              ·
                refine ⟨64562547146596337777317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344333584781847134812357 64562547146596337777317)
                ·
                  refine ⟨12105477589986813333247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64562547146596337777317 12105477589986813333247)
                  ·
                    rfl

theorem cell22_106089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 4].length) (baseStart_106089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106089 prefixEnd_106089 := by exact prefixLift 106089
  have htrace : WordTrace (prefixWord ++ tailWord_106089) baseStart_106089 baseEnd_106089 := by
    simpa [prefixWord, tailWord_106089, baseEnd_106089] using wordTrace_append hprefix tailTrace_106089
  have hstable : (prefixWord ++ tailWord_106089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106089).length < 2 ^ (prefixWord ++ tailWord_106089).sum := by decide
  have hdescent : baseEnd_106089 < baseStart_106089 := by decide
  rcases family_descends (prefixWord ++ tailWord_106089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106117 : List Nat := [1, 3, 1, 1, 4, 1, 3, 8]
def baseStart_106117 : Nat := 118140960795 + 106117 * 2 ^ 59
def prefixEnd_106117 : Nat := 4983230072969 + 3 ^ 40 * 106117 * 2
def baseEnd_106117 : Nat := 4036224193575300033295

theorem tailTrace_106117 : CollatzResearch.WordTrace tailWord_106117 prefixEnd_106117 4036224193575300033295 := by
  unfold tailWord_106117
  simp only [CollatzResearch.WordTrace]
  refine ⟨3870404956563707185836605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2580269971042471457224403 3870404956563707185836605)
  ·
    refine ⟨1451401858711390194688727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3870404956563707185836605 1451401858711390194688727)
    ·
      refine ⟨2177102788067085292033091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1451401858711390194688727 2177102788067085292033091)
      ·
        refine ⟨3265654182100627938049637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2177102788067085292033091 3265654182100627938049637)
        ·
          refine ⟨612310159143867738384307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3265654182100627938049637 612310159143867738384307)
          ·
            refine ⟨918465238715801607576461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612310159143867738384307 918465238715801607576461)
            ·
              refine ⟨344424464518425602841173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 918465238715801607576461 344424464518425602841173)
              ·
                refine ⟨4036224193575300033295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 344424464518425602841173 4036224193575300033295)
                ·
                  rfl

theorem cell22_106117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 8].length) (baseStart_106117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106117 prefixEnd_106117 := by exact prefixLift 106117
  have htrace : WordTrace (prefixWord ++ tailWord_106117) baseStart_106117 baseEnd_106117 := by
    simpa [prefixWord, tailWord_106117, baseEnd_106117] using wordTrace_append hprefix tailTrace_106117
  have hstable : (prefixWord ++ tailWord_106117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106117).length < 2 ^ (prefixWord ++ tailWord_106117).sum := by decide
  have hdescent : baseEnd_106117 < baseStart_106117 := by decide
  rcases family_descends (prefixWord ++ tailWord_106117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106147 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 2, 6]
def baseStart_106147 : Nat := 118140960795 + 106147 * 2 ^ 59
def prefixEnd_106147 : Nat := 4983230072969 + 3 ^ 40 * 106147 * 2
def baseEnd_106147 : Nat := 36336287355267622049563

theorem tailTrace_106147 : CollatzResearch.WordTrace tailWord_106147 prefixEnd_106147 36336287355267622049563 := by
  unfold tailWord_106147
  simp only [CollatzResearch.WordTrace]
  refine ⟨3871499146455022309428695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2580999430970014872952463 3871499146455022309428695)
  ·
    refine ⟨5807248719682533464143043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3871499146455022309428695 5807248719682533464143043)
    ·
      refine ⟨8710873079523800196214565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5807248719682533464143043 8710873079523800196214565)
      ·
        refine ⟨1633288702410712536790231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8710873079523800196214565 1633288702410712536790231)
        ·
          refine ⟨2449933053616068805185347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1633288702410712536790231 2449933053616068805185347)
          ·
            refine ⟨3674899580424103207778021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2449933053616068805185347 3674899580424103207778021)
            ·
              refine ⟨689043671329519351458379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3674899580424103207778021 689043671329519351458379)
              ·
                refine ⟨1033565506994279027187569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 689043671329519351458379 1033565506994279027187569)
                ·
                  refine ⟨775174130245709270390677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1033565506994279027187569 775174130245709270390677)
                  ·
                    refine ⟨36336287355267622049563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 775174130245709270390677 36336287355267622049563)
                    ·
                      rfl

theorem cell22_106147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 6].length) (baseStart_106147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106147 prefixEnd_106147 := by exact prefixLift 106147
  have htrace : WordTrace (prefixWord ++ tailWord_106147) baseStart_106147 baseEnd_106147 := by
    simpa [prefixWord, tailWord_106147, baseEnd_106147] using wordTrace_append hprefix tailTrace_106147
  have hstable : (prefixWord ++ tailWord_106147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106147).length < 2 ^ (prefixWord ++ tailWord_106147).sum := by decide
  have hdescent : baseEnd_106147 < baseStart_106147 := by decide
  rcases family_descends (prefixWord ++ tailWord_106147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106196 : List Nat := [2, 4, 1, 3, 1, 1, 1, 4, 5]
def baseStart_106196 : Nat := 118140960795 + 106196 * 2 ^ 59
def prefixEnd_106196 : Nat := 4983230072969 + 3 ^ 40 * 106196 * 2
def baseEnd_106196 : Nat := 12117687018882609191471

theorem tailTrace_106196 : CollatzResearch.WordTrace tailWord_106196 prefixEnd_106196 12117687018882609191471 := by
  unfold tailWord_106196
  simp only [CollatzResearch.WordTrace]
  refine ⟨1936643161638751838981221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2582190882185002451974961 1936643161638751838981221)
  ·
    refine ⟨363120592807265969808979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1936643161638751838981221 363120592807265969808979)
    ·
      refine ⟨544680889210898954713469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 363120592807265969808979 544680889210898954713469)
      ·
        refine ⟨204255333454087108017551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 544680889210898954713469 204255333454087108017551)
        ·
          refine ⟨306383000181130662026327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204255333454087108017551 306383000181130662026327)
          ·
            refine ⟨459574500271695993039491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306383000181130662026327 459574500271695993039491)
            ·
              refine ⟨689361750407543989559237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459574500271695993039491 689361750407543989559237)
              ·
                refine ⟨129255328201414498042357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 689361750407543989559237 129255328201414498042357)
                ·
                  refine ⟨12117687018882609191471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129255328201414498042357 12117687018882609191471)
                  ·
                    rfl

theorem cell22_106196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_106196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106196 prefixEnd_106196 := by exact prefixLift 106196
  have htrace : WordTrace (prefixWord ++ tailWord_106196) baseStart_106196 baseEnd_106196 := by
    simpa [prefixWord, tailWord_106196, baseEnd_106196] using wordTrace_append hprefix tailTrace_106196
  have hstable : (prefixWord ++ tailWord_106196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106196).length < 2 ^ (prefixWord ++ tailWord_106196).sum := by decide
  have hdescent : baseEnd_106196 < baseStart_106196 := by decide
  rcases family_descends (prefixWord ++ tailWord_106196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106211 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 2, 5]
def baseStart_106211 : Nat := 118140960795 + 106211 * 2 ^ 59
def prefixEnd_106211 : Nat := 4983230072969 + 3 ^ 40 * 106211 * 2
def baseEnd_106211 : Nat := 36358195863192788449367

theorem tailTrace_106211 : CollatzResearch.WordTrace tailWord_106211 prefixEnd_106211 36358195863192788449367 := by
  unfold tailWord_106211
  simp only [CollatzResearch.WordTrace]
  refine ⟨3873833418223161239758487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2582555612148774159838991 3873833418223161239758487)
  ·
    refine ⟨5810750127334741859637731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3873833418223161239758487 5810750127334741859637731)
    ·
      refine ⟨8716125191002112789456597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5810750127334741859637731 8716125191002112789456597)
      ·
        refine ⟨204284184164112018502889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 8716125191002112789456597 204284184164112018502889)
        ·
          refine ⟨153213138123084013877167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204284184164112018502889 153213138123084013877167)
          ·
            refine ⟨229819707184626020815751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153213138123084013877167 229819707184626020815751)
            ·
              refine ⟨344729560776939031223627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229819707184626020815751 344729560776939031223627)
              ·
                refine ⟨517094341165408546835441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 344729560776939031223627 517094341165408546835441)
                ·
                  refine ⟨387820755874056410126581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 517094341165408546835441 387820755874056410126581)
                  ·
                    refine ⟨36358195863192788449367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 387820755874056410126581 36358195863192788449367)
                    ·
                      rfl

theorem cell22_106211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 5].length) (baseStart_106211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106211 prefixEnd_106211 := by exact prefixLift 106211
  have htrace : WordTrace (prefixWord ++ tailWord_106211) baseStart_106211 baseEnd_106211 := by
    simpa [prefixWord, tailWord_106211, baseEnd_106211] using wordTrace_append hprefix tailTrace_106211
  have hstable : (prefixWord ++ tailWord_106211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106211).length < 2 ^ (prefixWord ++ tailWord_106211).sum := by decide
  have hdescent : baseEnd_106211 < baseStart_106211 := by decide
  rcases family_descends (prefixWord ++ tailWord_106211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106226 : List Nat := [3, 2, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_106226 : Nat := 118140960795 + 106226 * 2 ^ 59
def prefixEnd_106226 : Nat := 4983230072969 + 3 ^ 40 * 106226 * 2
def baseEnd_106226 : Nat := 36363330669737749324321

theorem tailTrace_106226 : CollatzResearch.WordTrace tailWord_106226 prefixEnd_106226 36363330669737749324321 := by
  unfold tailWord_106226
  simp only [CollatzResearch.WordTrace]
  refine ⟨968595128292204700388633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2582920342112545867703021 968595128292204700388633)
  ·
    refine ⟨726446346219153525291475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 968595128292204700388633 726446346219153525291475)
    ·
      refine ⟨1089669519328730287937213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 726446346219153525291475 1089669519328730287937213)
      ·
        refine ⟨408626069748273857976455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1089669519328730287937213 408626069748273857976455)
        ·
          refine ⟨612939104622410786964683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408626069748273857976455 612939104622410786964683)
          ·
            refine ⟨919408656933616180447025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612939104622410786964683 919408656933616180447025)
            ·
              refine ⟨689556492700212135335269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919408656933616180447025 689556492700212135335269)
              ·
                refine ⟨129291842381289775375363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 689556492700212135335269 129291842381289775375363)
                ·
                  refine ⟨193937763571934663063045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129291842381289775375363 193937763571934663063045)
                  ·
                    refine ⟨36363330669737749324321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 193937763571934663063045 36363330669737749324321)
                    ·
                      rfl

theorem cell22_106226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_106226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106226 prefixEnd_106226 := by exact prefixLift 106226
  have htrace : WordTrace (prefixWord ++ tailWord_106226) baseStart_106226 baseEnd_106226 := by
    simpa [prefixWord, tailWord_106226, baseEnd_106226] using wordTrace_append hprefix tailTrace_106226
  have hstable : (prefixWord ++ tailWord_106226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106226).length < 2 ^ (prefixWord ++ tailWord_106226).sum := by decide
  have hdescent : baseEnd_106226 < baseStart_106226 := by decide
  rcases family_descends (prefixWord ++ tailWord_106226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106239 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 1, 5]
def baseStart_106239 : Nat := 118140960795 + 106239 * 2 ^ 59
def prefixEnd_106239 : Nat := 4983230072969 + 3 ^ 40 * 106239 * 2
def baseEnd_106239 : Nat := 36367780835410048749281

theorem tailTrace_106239 : CollatzResearch.WordTrace tailWord_106239 prefixEnd_106239 36367780835410048749281 := by
  unfold tailWord_106239
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874854662121722021777771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2583236441414481347851847 3874854662121722021777771)
  ·
    refine ⟨5812281993182583032666657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3874854662121722021777771 5812281993182583032666657)
    ·
      refine ⟨4359211494886937274499993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5812281993182583032666657 4359211494886937274499993)
      ·
        refine ⟨3269408621165202955874995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4359211494886937274499993 3269408621165202955874995)
        ·
          refine ⟨4904112931747804433812493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3269408621165202955874995 4904112931747804433812493)
          ·
            refine ⟨1839042349405426662679685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4904112931747804433812493 1839042349405426662679685)
            ·
              refine ⟨344820440513517499252441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1839042349405426662679685 344820440513517499252441)
              ·
                refine ⟨258615330385138124439331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 344820440513517499252441 258615330385138124439331)
                ·
                  refine ⟨387922995577707186658997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258615330385138124439331 387922995577707186658997)
                  ·
                    refine ⟨36367780835410048749281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 387922995577707186658997 36367780835410048749281)
                    ·
                      rfl

theorem cell22_106239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_106239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106239 prefixEnd_106239 := by exact prefixLift 106239
  have htrace : WordTrace (prefixWord ++ tailWord_106239) baseStart_106239 baseEnd_106239 := by
    simpa [prefixWord, tailWord_106239, baseEnd_106239] using wordTrace_append hprefix tailTrace_106239
  have hstable : (prefixWord ++ tailWord_106239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106239).length < 2 ^ (prefixWord ++ tailWord_106239).sum := by decide
  have hdescent : baseEnd_106239 < baseStart_106239 := by decide
  rcases family_descends (prefixWord ++ tailWord_106239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106241 : List Nat := [1, 2, 4, 1, 1, 1, 3, 5, 4]
def baseStart_106241 : Nat := 118140960795 + 106241 * 2 ^ 59
def prefixEnd_106241 : Nat := 4983230072969 + 3 ^ 40 * 106241 * 2
def baseEnd_106241 : Nat := 12122821825427570066425

theorem tailTrace_106241 : CollatzResearch.WordTrace tailWord_106241 prefixEnd_106241 12122821825427570066425 := by
  unfold tailWord_106241
  simp only [CollatzResearch.WordTrace]
  refine ⟨3874927608114476363350577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2583285072076317575567051 3874927608114476363350577)
  ·
    refine ⟨2906195706085857272512933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3874927608114476363350577 2906195706085857272512933)
    ·
      refine ⟨544911694891098238596175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2906195706085857272512933 544911694891098238596175)
      ·
        refine ⟨817367542336647357894263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 544911694891098238596175 817367542336647357894263)
        ·
          refine ⟨1226051313504971036841395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 817367542336647357894263 1226051313504971036841395)
          ·
            refine ⟨1839076970257456555262093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1226051313504971036841395 1839076970257456555262093)
            ·
              refine ⟨689653863846546208223285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1839076970257456555262093 689653863846546208223285)
              ·
                refine ⟨64655049735613707020933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 689653863846546208223285 64655049735613707020933)
                ·
                  refine ⟨12122821825427570066425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64655049735613707020933 12122821825427570066425)
                  ·
                    rfl

theorem cell22_106241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 4].length) (baseStart_106241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106241 prefixEnd_106241 := by exact prefixLift 106241
  have htrace : WordTrace (prefixWord ++ tailWord_106241) baseStart_106241 baseEnd_106241 := by
    simpa [prefixWord, tailWord_106241, baseEnd_106241] using wordTrace_append hprefix tailTrace_106241
  have hstable : (prefixWord ++ tailWord_106241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106241).length < 2 ^ (prefixWord ++ tailWord_106241).sum := by decide
  have hdescent : baseEnd_106241 < baseStart_106241 := by decide
  rcases family_descends (prefixWord ++ tailWord_106241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106258 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 6]
def baseStart_106258 : Nat := 118140960795 + 106258 * 2 ^ 59
def prefixEnd_106258 : Nat := 4983230072969 + 3 ^ 40 * 106258 * 2
def baseEnd_106258 : Nat := 12124761641233444174741

theorem tailTrace_106258 : CollatzResearch.WordTrace tailWord_106258 prefixEnd_106258 12124761641233444174741 := by
  unfold tailWord_106258
  simp only [CollatzResearch.WordTrace]
  refine ⟨968886912263222066679857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2583698432701925511146285 968886912263222066679857)
  ·
    refine ⟨726665184197416550009893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 968886912263222066679857 726665184197416550009893)
    ·
      refine ⟨136249722037015603126855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 726665184197416550009893 136249722037015603126855)
      ·
        refine ⟨204374583055523404690283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136249722037015603126855 204374583055523404690283)
        ·
          refine ⟨306561874583285107035425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204374583055523404690283 306561874583285107035425)
          ·
            refine ⟨229921405937463830276569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306561874583285107035425 229921405937463830276569)
            ·
              refine ⟨172441054453097872707427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229921405937463830276569 172441054453097872707427)
              ·
                refine ⟨258661581679646809061141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172441054453097872707427 258661581679646809061141)
                ·
                  refine ⟨12124761641233444174741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 258661581679646809061141 12124761641233444174741)
                  ·
                    rfl

theorem cell22_106258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_106258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106258 prefixEnd_106258 := by exact prefixLift 106258
  have htrace : WordTrace (prefixWord ++ tailWord_106258) baseStart_106258 baseEnd_106258 := by
    simpa [prefixWord, tailWord_106258, baseEnd_106258] using wordTrace_append hprefix tailTrace_106258
  have hstable : (prefixWord ++ tailWord_106258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106258).length < 2 ^ (prefixWord ++ tailWord_106258).sum := by decide
  have hdescent : baseEnd_106258 < baseStart_106258 := by decide
  rcases family_descends (prefixWord ++ tailWord_106258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106314 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 7]
def baseStart_106314 : Nat := 118140960795 + 106314 * 2 ^ 59
def prefixEnd_106314 : Nat := 4983230072969 + 3 ^ 40 * 106314 * 2
def baseEnd_106314 : Nat := 12131151622711617708017

theorem tailTrace_106314 : CollatzResearch.WordTrace tailWord_106314 prefixEnd_106314 12131151622711617708017 := by
  unfold tailWord_106314
  simp only [CollatzResearch.WordTrace]
  refine ⟨969397534212502457689499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2585060091233339887171997 969397534212502457689499)
  ·
    refine ⟨1454096301318753686534249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 969397534212502457689499 1454096301318753686534249)
    ·
      refine ⟨1090572225989065264900687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1454096301318753686534249 1090572225989065264900687)
      ·
        refine ⟨1635858338983597897351031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1090572225989065264900687 1635858338983597897351031)
        ·
          refine ⟨2453787508475396846026547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1635858338983597897351031 2453787508475396846026547)
          ·
            refine ⟨3680681262713095269039821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453787508475396846026547 3680681262713095269039821)
            ·
              refine ⟨1380255473517410725889933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3680681262713095269039821 1380255473517410725889933)
              ·
                refine ⟨517595802569029022208725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1380255473517410725889933 517595802569029022208725)
                ·
                  refine ⟨12131151622711617708017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 517595802569029022208725 12131151622711617708017)
                  ·
                    rfl

theorem cell22_106314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_106314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106314 prefixEnd_106314 := by exact prefixLift 106314
  have htrace : WordTrace (prefixWord ++ tailWord_106314) baseStart_106314 baseEnd_106314 := by
    simpa [prefixWord, tailWord_106314, baseEnd_106314] using wordTrace_append hprefix tailTrace_106314
  have hstable : (prefixWord ++ tailWord_106314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106314).length < 2 ^ (prefixWord ++ tailWord_106314).sum := by decide
  have hdescent : baseEnd_106314 < baseStart_106314 := by decide
  rcases family_descends (prefixWord ++ tailWord_106314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106329 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 1, 7]
def baseStart_106329 : Nat := 118140960795 + 106329 * 2 ^ 59
def prefixEnd_106329 : Nat := 4983230072969 + 3 ^ 40 * 106329 * 2
def baseEnd_106329 : Nat := 36398589674679813999005

theorem tailTrace_106329 : CollatzResearch.WordTrace tailWord_106329 prefixEnd_106329 36398589674679813999005 := by
  unfold tailWord_106329
  simp only [CollatzResearch.WordTrace]
  refine ⟨3878137231795667392554041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2585424821197111595036027 3878137231795667392554041)
  ·
    refine ⟨2908602923846750544415531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3878137231795667392554041 2908602923846750544415531)
    ·
      refine ⟨4362904385770125816623297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2908602923846750544415531 4362904385770125816623297)
      ·
        refine ⟨3272178289327594362467473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4362904385770125816623297 3272178289327594362467473)
        ·
          refine ⟨2454133716995695771850605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3272178289327594362467473 2454133716995695771850605)
          ·
            refine ⟨920300143873385914443977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2454133716995695771850605 920300143873385914443977)
            ·
              refine ⟨690225107905039435832983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 920300143873385914443977 690225107905039435832983)
              ·
                refine ⟨1035337661857559153749475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 690225107905039435832983 1035337661857559153749475)
                ·
                  refine ⟨1553006492786338730624213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1035337661857559153749475 1553006492786338730624213)
                  ·
                    refine ⟨36398589674679813999005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1553006492786338730624213 36398589674679813999005)
                    ·
                      rfl

theorem cell22_106329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_106329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106329 prefixEnd_106329 := by exact prefixLift 106329
  have htrace : WordTrace (prefixWord ++ tailWord_106329) baseStart_106329 baseEnd_106329 := by
    simpa [prefixWord, tailWord_106329, baseEnd_106329] using wordTrace_append hprefix tailTrace_106329
  have hstable : (prefixWord ++ tailWord_106329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106329).length < 2 ^ (prefixWord ++ tailWord_106329).sum := by decide
  have hdescent : baseEnd_106329 < baseStart_106329 := by decide
  rcases family_descends (prefixWord ++ tailWord_106329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106391 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 1, 5]
def baseStart_106391 : Nat := 118140960795 + 106391 * 2 ^ 59
def prefixEnd_106391 : Nat := 4983230072969 + 3 ^ 40 * 106391 * 2
def baseEnd_106391 : Nat := 36419813541732318948815

theorem tailTrace_106391 : CollatzResearch.WordTrace tailWord_106391 prefixEnd_106391 36419813541732318948815 := by
  unfold tailWord_106391
  simp only [CollatzResearch.WordTrace]
  refine ⟨3880398557571051981311027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2586932371714034654207351 3880398557571051981311027)
  ·
    refine ⟨5820597836356577971966541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3880398557571051981311027 5820597836356577971966541)
    ·
      refine ⟨2182724188633716739487453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5820597836356577971966541 2182724188633716739487453)
      ·
        refine ⟨818521570737643777307795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2182724188633716739487453 818521570737643777307795)
        ·
          refine ⟨1227782356106465665961693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 818521570737643777307795 1227782356106465665961693)
          ·
            refine ⟨460418383539924624735635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1227782356106465665961693 460418383539924624735635)
            ·
              refine ⟨690627575309886937103453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460418383539924624735635 690627575309886937103453)
              ·
                refine ⟨258985340741207601413795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 690627575309886937103453 258985340741207601413795)
                ·
                  refine ⟨388478011111811402120693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 258985340741207601413795 388478011111811402120693)
                  ·
                    refine ⟨36419813541732318948815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 388478011111811402120693 36419813541732318948815)
                    ·
                      rfl

theorem cell22_106391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_106391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106391 prefixEnd_106391 := by exact prefixLift 106391
  have htrace : WordTrace (prefixWord ++ tailWord_106391) baseStart_106391 baseEnd_106391 := by
    simpa [prefixWord, tailWord_106391, baseEnd_106391] using wordTrace_append hprefix tailTrace_106391
  have hstable : (prefixWord ++ tailWord_106391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106391).length < 2 ^ (prefixWord ++ tailWord_106391).sum := by decide
  have hdescent : baseEnd_106391 < baseStart_106391 := by decide
  rcases family_descends (prefixWord ++ tailWord_106391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106421 : List Nat := [1, 3, 3, 2, 1, 3, 9]
def baseStart_106421 : Nat := 118140960795 + 106421 * 2 ^ 59
def prefixEnd_106421 : Nat := 4983230072969 + 3 ^ 40 * 106421 * 2
def baseEnd_106421 : Nat := 1349262339067490396249

theorem tailTrace_106421 : CollatzResearch.WordTrace tailWord_106421 prefixEnd_106421 1349262339067490396249 := by
  unfold tailWord_106421
  simp only [CollatzResearch.WordTrace]
  refine ⟨3881492747462367104903117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2587661831641578069935411 3881492747462367104903117)
  ·
    refine ⟨1455559780298387664338669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3881492747462367104903117 1455559780298387664338669)
    ·
      refine ⟨545834917611895374127001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1455559780298387664338669 545834917611895374127001)
      ·
        refine ⟨409376188208921530595251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 545834917611895374127001 409376188208921530595251)
        ·
          refine ⟨614064282313382295892877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409376188208921530595251 614064282313382295892877)
          ·
            refine ⟨230274105867518360959829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 614064282313382295892877 230274105867518360959829)
            ·
              refine ⟨1349262339067490396249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 230274105867518360959829 1349262339067490396249)
              ·
                rfl

theorem cell22_106421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 9].length) (baseStart_106421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106421 prefixEnd_106421 := by exact prefixLift 106421
  have htrace : WordTrace (prefixWord ++ tailWord_106421) baseStart_106421 baseEnd_106421 := by
    simpa [prefixWord, tailWord_106421, baseEnd_106421] using wordTrace_append hprefix tailTrace_106421
  have hstable : (prefixWord ++ tailWord_106421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106421).length < 2 ^ (prefixWord ++ tailWord_106421).sum := by decide
  have hdescent : baseEnd_106421 < baseStart_106421 := by decide
  rcases family_descends (prefixWord ++ tailWord_106421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106545 : List Nat := [1, 2, 2, 3, 1, 4, 1, 4, 4]
def baseStart_106545 : Nat := 118140960795 + 106545 * 2 ^ 59
def prefixEnd_106545 : Nat := 4983230072969 + 3 ^ 40 * 106545 * 2
def baseEnd_106545 : Nat := 12157510296309083532781

theorem tailTrace_106545 : CollatzResearch.WordTrace tailWord_106545 prefixEnd_106545 12157510296309083532781 := by
  unfold tailWord_106545
  simp only [CollatzResearch.WordTrace]
  refine ⟨3886015399013136282417089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2590676932675424188278059 3886015399013136282417089)
  ·
    refine ⟨2914511549259852211812817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3886015399013136282417089 2914511549259852211812817)
    ·
      refine ⟨2185883661944889158859613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2914511549259852211812817 2185883661944889158859613)
      ·
        refine ⟨819706373229333434572355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2185883661944889158859613 819706373229333434572355)
        ·
          refine ⟨1229559559844000151858533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819706373229333434572355 1229559559844000151858533)
          ·
            refine ⟨230542417470750028473475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1229559559844000151858533 230542417470750028473475)
            ·
              refine ⟨345813626206125042710213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230542417470750028473475 345813626206125042710213)
              ·
                refine ⟨64840054913648445508165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 345813626206125042710213 64840054913648445508165)
                ·
                  refine ⟨12157510296309083532781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64840054913648445508165 12157510296309083532781)
                  ·
                    rfl

theorem cell22_106545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 4].length) (baseStart_106545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106545 prefixEnd_106545 := by exact prefixLift 106545
  have htrace : WordTrace (prefixWord ++ tailWord_106545) baseStart_106545 baseEnd_106545 := by
    simpa [prefixWord, tailWord_106545, baseEnd_106545] using wordTrace_append hprefix tailTrace_106545
  have hstable : (prefixWord ++ tailWord_106545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106545).length < 2 ^ (prefixWord ++ tailWord_106545).sum := by decide
  have hdescent : baseEnd_106545 < baseStart_106545 := by decide
  rcases family_descends (prefixWord ++ tailWord_106545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106560 : List Nat := [2, 1, 1, 2, 2, 4, 2, 3, 2, 3]
def baseStart_106560 : Nat := 118140960795 + 106560 * 2 ^ 59
def prefixEnd_106560 : Nat := 4983230072969 + 3 ^ 40 * 106560 * 2
def baseEnd_106560 : Nat := 36477665695472211473297

theorem tailTrace_106560 : CollatzResearch.WordTrace tailWord_106560 prefixEnd_106560 36477665695472211473297 := by
  unfold tailWord_106560
  simp only [CollatzResearch.WordTrace]
  refine ⟨1943281246979396922106567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2591041662639195896142089 1943281246979396922106567)
  ·
    refine ⟨2914921870469095383159851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1943281246979396922106567 2914921870469095383159851)
    ·
      refine ⟨4372382805703643074739777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2914921870469095383159851 4372382805703643074739777)
      ·
        refine ⟨3279287104277732306054833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4372382805703643074739777 3279287104277732306054833)
        ·
          refine ⟨2459465328208299229541125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3279287104277732306054833 2459465328208299229541125)
          ·
            refine ⟨461149749039056105538961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2459465328208299229541125 461149749039056105538961)
            ·
              refine ⟨345862311779292079154221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461149749039056105538961 345862311779292079154221)
              ·
                refine ⟨129698366917234529682833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345862311779292079154221 129698366917234529682833)
                ·
                  refine ⟨97273775187925897262125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129698366917234529682833 97273775187925897262125)
                  ·
                    refine ⟨36477665695472211473297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97273775187925897262125 36477665695472211473297)
                    ·
                      rfl

theorem cell22_106560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 2, 3].length) (baseStart_106560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106560 prefixEnd_106560 := by exact prefixLift 106560
  have htrace : WordTrace (prefixWord ++ tailWord_106560) baseStart_106560 baseEnd_106560 := by
    simpa [prefixWord, tailWord_106560, baseEnd_106560] using wordTrace_append hprefix tailTrace_106560
  have hstable : (prefixWord ++ tailWord_106560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106560).length < 2 ^ (prefixWord ++ tailWord_106560).sum := by decide
  have hdescent : baseEnd_106560 < baseStart_106560 := by decide
  rcases family_descends (prefixWord ++ tailWord_106560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106571 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 2, 7]
def baseStart_106571 : Nat := 118140960795 + 106571 * 2 ^ 59
def prefixEnd_106571 : Nat := 4983230072969 + 3 ^ 40 * 106571 * 2
def baseEnd_106571 : Nat := 36481431220271849448263

theorem tailTrace_106571 : CollatzResearch.WordTrace tailWord_106571 prefixEnd_106571 36481431220271849448263 := by
  unfold tailWord_106571
  simp only [CollatzResearch.WordTrace]
  refine ⟨3886963696918942722863567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2591309131279295148575711 3886963696918942722863567)
  ·
    refine ⟨5830445545378414084295351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3886963696918942722863567 5830445545378414084295351)
    ·
      refine ⟨8745668318067621126443027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5830445545378414084295351 8745668318067621126443027)
      ·
        refine ⟨13118502477101431689664541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8745668318067621126443027 13118502477101431689664541)
        ·
          refine ⟨4919438428913036883624203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13118502477101431689664541 4919438428913036883624203)
          ·
            refine ⟨7379157643369555325436305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919438428913036883624203 7379157643369555325436305)
            ·
              refine ⟨5534368232527166494077229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7379157643369555325436305 5534368232527166494077229)
              ·
                refine ⟨2075388087197687435278961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5534368232527166494077229 2075388087197687435278961)
                ·
                  refine ⟨1556541065398265576459221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2075388087197687435278961 1556541065398265576459221)
                  ·
                    refine ⟨36481431220271849448263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1556541065398265576459221 36481431220271849448263)
                    ·
                      rfl

theorem cell22_106571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 7].length) (baseStart_106571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106571 prefixEnd_106571 := by exact prefixLift 106571
  have htrace : WordTrace (prefixWord ++ tailWord_106571) baseStart_106571 baseEnd_106571 := by
    simpa [prefixWord, tailWord_106571, baseEnd_106571] using wordTrace_append hprefix tailTrace_106571
  have hstable : (prefixWord ++ tailWord_106571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106571).length < 2 ^ (prefixWord ++ tailWord_106571).sum := by decide
  have hdescent : baseEnd_106571 < baseStart_106571 := by decide
  rcases family_descends (prefixWord ++ tailWord_106571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106669 : List Nat := [1, 5, 2, 1, 2, 3, 2, 1, 5]
def baseStart_106669 : Nat := 118140960795 + 106669 * 2 ^ 59
def prefixEnd_106669 : Nat := 4983230072969 + 3 ^ 40 * 106669 * 2
def baseEnd_106669 : Nat := 12171659541010753499321

theorem tailTrace_106669 : CollatzResearch.WordTrace tailWord_106669 prefixEnd_106669 12171659541010753499321 := by
  unfold tailWord_106669
  simp only [CollatzResearch.WordTrace]
  refine ⟨3890538050563905459931061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2593692033709270306620707 3890538050563905459931061)
  ·
    refine ⟨364737942240366136868537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3890538050563905459931061 364737942240366136868537)
    ·
      refine ⟨273553456680274602651403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364737942240366136868537 273553456680274602651403)
      ·
        refine ⟨410330185020411903977105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273553456680274602651403 410330185020411903977105)
        ·
          refine ⟨307747638765308927982829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410330185020411903977105 307747638765308927982829)
          ·
            refine ⟨115405364536990847993561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307747638765308927982829 115405364536990847993561)
            ·
              refine ⟨86554023402743135995171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115405364536990847993561 86554023402743135995171)
              ·
                refine ⟨129831035104114703992757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86554023402743135995171 129831035104114703992757)
                ·
                  refine ⟨12171659541010753499321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129831035104114703992757 12171659541010753499321)
                  ·
                    rfl

theorem cell22_106669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_106669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106669 prefixEnd_106669 := by exact prefixLift 106669
  have htrace : WordTrace (prefixWord ++ tailWord_106669) baseStart_106669 baseEnd_106669 := by
    simpa [prefixWord, tailWord_106669, baseEnd_106669] using wordTrace_append hprefix tailTrace_106669
  have hstable : (prefixWord ++ tailWord_106669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106669).length < 2 ^ (prefixWord ++ tailWord_106669).sum := by decide
  have hdescent : baseEnd_106669 < baseStart_106669 := by decide
  rcases family_descends (prefixWord ++ tailWord_106669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106693 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_106693 : Nat := 118140960795 + 106693 * 2 ^ 59
def prefixEnd_106693 : Nat := 4983230072969 + 3 ^ 40 * 106693 * 2
def baseEnd_106693 : Nat := 36523194313504197897889

theorem tailTrace_106693 : CollatzResearch.WordTrace tailWord_106693 prefixEnd_106693 36523194313504197897889 := by
  unfold tailWord_106693
  simp only [CollatzResearch.WordTrace]
  refine ⟨3891413402476957558804733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2594275601651305039203155 3891413402476957558804733)
  ·
    refine ⟨1459280025928859084551775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3891413402476957558804733 1459280025928859084551775)
    ·
      refine ⟨2188920038893288626827663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1459280025928859084551775 2188920038893288626827663)
      ·
        refine ⟨3283380058339932940241495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2188920038893288626827663 3283380058339932940241495)
        ·
          refine ⟨4925070087509899410362243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283380058339932940241495 4925070087509899410362243)
          ·
            refine ⟨7387605131264849115543365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925070087509899410362243 7387605131264849115543365)
            ·
              refine ⟨1385175962112159209164381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7387605131264849115543365 1385175962112159209164381)
              ·
                refine ⟨519440985792059703436643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1385175962112159209164381 519440985792059703436643)
                ·
                  refine ⟨779161478688089555154965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 519440985792059703436643 779161478688089555154965)
                  ·
                    refine ⟨36523194313504197897889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 779161478688089555154965 36523194313504197897889)
                    ·
                      rfl

theorem cell22_106693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_106693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106693 prefixEnd_106693 := by exact prefixLift 106693
  have htrace : WordTrace (prefixWord ++ tailWord_106693) baseStart_106693 baseEnd_106693 := by
    simpa [prefixWord, tailWord_106693, baseEnd_106693] using wordTrace_append hprefix tailTrace_106693
  have hstable : (prefixWord ++ tailWord_106693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106693).length < 2 ^ (prefixWord ++ tailWord_106693).sum := by decide
  have hdescent : baseEnd_106693 < baseStart_106693 := by decide
  rcases family_descends (prefixWord ++ tailWord_106693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106708 : List Nat := [2, 4, 1, 15]
def baseStart_106708 : Nat := 118140960795 + 106708 * 2 ^ 59
def prefixEnd_106708 : Nat := 4983230072969 + 3 ^ 40 * 106708 * 2
def baseEnd_106708 : Nat := 50107447352605156067

theorem tailTrace_106708 : CollatzResearch.WordTrace tailWord_106708 prefixEnd_106708 50107447352605156067 := by
  unfold tailWord_106708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1945980248711307560300389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2594640331615076747067185 1945980248711307560300389)
  ·
    refine ⟨364871296633370167556323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1945980248711307560300389 364871296633370167556323)
    ·
      refine ⟨547306944950055251334485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364871296633370167556323 547306944950055251334485)
      ·
        refine ⟨50107447352605156067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 547306944950055251334485 50107447352605156067)
        ·
          rfl

theorem cell22_106708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 15].length) (baseStart_106708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106708 prefixEnd_106708 := by exact prefixLift 106708
  have htrace : WordTrace (prefixWord ++ tailWord_106708) baseStart_106708 baseEnd_106708 := by
    simpa [prefixWord, tailWord_106708, baseEnd_106708] using wordTrace_append hprefix tailTrace_106708
  have hstable : (prefixWord ++ tailWord_106708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106708).length < 2 ^ (prefixWord ++ tailWord_106708).sum := by decide
  have hdescent : baseEnd_106708 < baseStart_106708 := by decide
  rcases family_descends (prefixWord ++ tailWord_106708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106712 : List Nat := [2, 1, 2, 2, 4, 1, 1, 4, 2, 3]
def baseStart_106712 : Nat := 118140960795 + 106712 * 2 ^ 59
def prefixEnd_106712 : Nat := 4983230072969 + 3 ^ 40 * 106712 * 2
def baseEnd_106712 : Nat := 36529698401794481672831

theorem tailTrace_106712 : CollatzResearch.WordTrace tailWord_106712 prefixEnd_106712 36529698401794481672831 := by
  unfold tailWord_106712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946053194704061901873195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2594737592938749202497593 1946053194704061901873195)
  ·
    refine ⟨2919079792056092852809793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1946053194704061901873195 2919079792056092852809793)
    ·
      refine ⟨2189309844042069639607345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2919079792056092852809793 2189309844042069639607345)
      ·
        refine ⟨1641982383031552229705509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2189309844042069639607345 1641982383031552229705509)
        ·
          refine ⟨307871696818416043069783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1641982383031552229705509 307871696818416043069783)
          ·
            refine ⟨461807545227624064604675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307871696818416043069783 461807545227624064604675)
            ·
              refine ⟨692711317841436096907013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461807545227624064604675 692711317841436096907013)
              ·
                refine ⟨129883372095269268170065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 692711317841436096907013 129883372095269268170065)
                ·
                  refine ⟨97412529071451951127549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129883372095269268170065 97412529071451951127549)
                  ·
                    refine ⟨36529698401794481672831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97412529071451951127549 36529698401794481672831)
                    ·
                      rfl

theorem cell22_106712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_106712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106712 prefixEnd_106712 := by exact prefixLift 106712
  have htrace : WordTrace (prefixWord ++ tailWord_106712) baseStart_106712 baseEnd_106712 := by
    simpa [prefixWord, tailWord_106712, baseEnd_106712] using wordTrace_append hprefix tailTrace_106712
  have hstable : (prefixWord ++ tailWord_106712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106712).length < 2 ^ (prefixWord ++ tailWord_106712).sum := by decide
  have hdescent : baseEnd_106712 < baseStart_106712 := by decide
  rcases family_descends (prefixWord ++ tailWord_106712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106725 : List Nat := [1, 3, 1, 4, 2, 1, 3, 7]
def baseStart_106725 : Nat := 118140960795 + 106725 * 2 ^ 59
def prefixEnd_106725 : Nat := 4983230072969 + 3 ^ 40 * 106725 * 2
def baseEnd_106725 : Nat := 4059349840829642344199

theorem tailTrace_106725 : CollatzResearch.WordTrace tailWord_106725 prefixEnd_106725 4059349840829642344199 := by
  unfold tailWord_106725
  simp only [CollatzResearch.WordTrace]
  refine ⟨3892580538361027023969629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2595053692240684682646419 3892580538361027023969629)
  ·
    refine ⟨1459717701885385133988611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3892580538361027023969629 1459717701885385133988611)
    ·
      refine ⟨2189576552828077700982917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1459717701885385133988611 2189576552828077700982917)
      ·
        refine ⟨410545603655264568934297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2189576552828077700982917 410545603655264568934297)
        ·
          refine ⟨307909202741448426700723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410545603655264568934297 307909202741448426700723)
          ·
            refine ⟨461863804112172640051085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307909202741448426700723 461863804112172640051085)
            ·
              refine ⟨173198926542064740019157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461863804112172640051085 173198926542064740019157)
              ·
                refine ⟨4059349840829642344199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 173198926542064740019157 4059349840829642344199)
                ·
                  rfl

theorem cell22_106725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 7].length) (baseStart_106725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106725 prefixEnd_106725 := by exact prefixLift 106725
  have htrace : WordTrace (prefixWord ++ tailWord_106725) baseStart_106725 baseEnd_106725 := by
    simpa [prefixWord, tailWord_106725, baseEnd_106725] using wordTrace_append hprefix tailTrace_106725
  have hstable : (prefixWord ++ tailWord_106725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106725).length < 2 ^ (prefixWord ++ tailWord_106725).sum := by decide
  have hdescent : baseEnd_106725 < baseStart_106725 := by decide
  rcases family_descends (prefixWord ++ tailWord_106725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106768 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 2, 11]
def baseStart_106768 : Nat := 118140960795 + 106768 * 2 ^ 59
def prefixEnd_106768 : Nat := 4983230072969 + 3 ^ 40 * 106768 * 2
def baseEnd_106768 : Nat := 36548868346229002272659

theorem tailTrace_106768 : CollatzResearch.WordTrace tailWord_106768 prefixEnd_106768 36548868346229002272659 := by
  unfold tailWord_106768
  simp only [CollatzResearch.WordTrace]
  refine ⟨1947074438602622683892479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2596099251470163578523305 1947074438602622683892479)
  ·
    refine ⟨2920611657903934025838719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1947074438602622683892479 2920611657903934025838719)
    ·
      refine ⟨4380917486855901038758079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2920611657903934025838719 4380917486855901038758079)
      ·
        refine ⟨6571376230283851558137119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4380917486855901038758079 6571376230283851558137119)
        ·
          refine ⟨9857064345425777337205679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6571376230283851558137119 9857064345425777337205679)
          ·
            refine ⟨14785596518138666005808519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9857064345425777337205679 14785596518138666005808519)
            ·
              refine ⟨22178394777207999008712779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14785596518138666005808519 22178394777207999008712779)
              ·
                refine ⟨33267592165811998513069169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22178394777207999008712779 33267592165811998513069169)
                ·
                  refine ⟨24950694124358998884801877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33267592165811998513069169 24950694124358998884801877)
                  ·
                    refine ⟨36548868346229002272659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 24950694124358998884801877 36548868346229002272659)
                    ·
                      rfl

theorem cell22_106768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_106768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106768 prefixEnd_106768 := by exact prefixLift 106768
  have htrace : WordTrace (prefixWord ++ tailWord_106768) baseStart_106768 baseEnd_106768 := by
    simpa [prefixWord, tailWord_106768, baseEnd_106768] using wordTrace_append hprefix tailTrace_106768
  have hstable : (prefixWord ++ tailWord_106768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106768).length < 2 ^ (prefixWord ++ tailWord_106768).sum := by decide
  have hdescent : baseEnd_106768 < baseStart_106768 := by decide
  rcases family_descends (prefixWord ++ tailWord_106768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106785 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 2, 5]
def baseStart_106785 : Nat := 118140960795 + 106785 * 2 ^ 59
def prefixEnd_106785 : Nat := 4983230072969 + 3 ^ 40 * 106785 * 2
def baseEnd_106785 : Nat := 36554687793646624597607

theorem tailTrace_106785 : CollatzResearch.WordTrace tailWord_106785 prefixEnd_106785 36554687793646624597607 := by
  unfold tailWord_106785
  simp only [CollatzResearch.WordTrace]
  refine ⟨3894768918143657271153809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2596512612095771514102539 3894768918143657271153809)
  ·
    refine ⟨2921076688607742953365357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3894768918143657271153809 2921076688607742953365357)
    ·
      refine ⟨1095403758227903607512009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2921076688607742953365357 1095403758227903607512009)
      ·
        refine ⟨821552818670927705634007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1095403758227903607512009 821552818670927705634007)
        ·
          refine ⟨1232329228006391558451011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821552818670927705634007 1232329228006391558451011)
          ·
            refine ⟨1848493842009587337676517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232329228006391558451011 1848493842009587337676517)
            ·
              refine ⟨346592595376797625814347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1848493842009587337676517 346592595376797625814347)
              ·
                refine ⟨519888893065196438721521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 346592595376797625814347 519888893065196438721521)
                ·
                  refine ⟨389916669798897329041141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519888893065196438721521 389916669798897329041141)
                  ·
                    refine ⟨36554687793646624597607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 389916669798897329041141 36554687793646624597607)
                    ·
                      rfl

theorem cell22_106785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_106785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106785 prefixEnd_106785 := by exact prefixLift 106785
  have htrace : WordTrace (prefixWord ++ tailWord_106785) baseStart_106785 baseEnd_106785 := by
    simpa [prefixWord, tailWord_106785, baseEnd_106785] using wordTrace_append hprefix tailTrace_106785
  have hstable : (prefixWord ++ tailWord_106785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106785).length < 2 ^ (prefixWord ++ tailWord_106785).sum := by decide
  have hdescent : baseEnd_106785 < baseStart_106785 := by decide
  rcases family_descends (prefixWord ++ tailWord_106785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106787 : List Nat := [1, 1, 1, 4, 2, 2, 5, 1, 5]
def baseStart_106787 : Nat := 118140960795 + 106787 * 2 ^ 59
def prefixEnd_106787 : Nat := 4983230072969 + 3 ^ 40 * 106787 * 2
def baseEnd_106787 : Nat := 12185124144839762015867

theorem tailTrace_106787 : CollatzResearch.WordTrace tailWord_106787 prefixEnd_106787 12185124144839762015867 := by
  unfold tailWord_106787
  simp only [CollatzResearch.WordTrace]
  refine ⟨3894841864136411612726615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2596561242757607741817743 3894841864136411612726615)
  ·
    refine ⟨5842262796204617419089923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3894841864136411612726615 5842262796204617419089923)
    ·
      refine ⟨8763394194306926128634885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5842262796204617419089923 8763394194306926128634885)
      ·
        refine ⟨1643136411432548649119041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8763394194306926128634885 1643136411432548649119041)
        ·
          refine ⟨1232352308574411486839281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1643136411432548649119041 1232352308574411486839281)
          ·
            refine ⟨924264231430808615129461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1232352308574411486839281 924264231430808615129461)
            ·
              refine ⟨86649771696638307668387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 924264231430808615129461 86649771696638307668387)
              ·
                refine ⟨129974657544957461502581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86649771696638307668387 129974657544957461502581)
                ·
                  refine ⟨12185124144839762015867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129974657544957461502581 12185124144839762015867)
                  ·
                    rfl

theorem cell22_106787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 1, 5].length) (baseStart_106787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106787 prefixEnd_106787 := by exact prefixLift 106787
  have htrace : WordTrace (prefixWord ++ tailWord_106787) baseStart_106787 baseEnd_106787 := by
    simpa [prefixWord, tailWord_106787, baseEnd_106787] using wordTrace_append hprefix tailTrace_106787
  have hstable : (prefixWord ++ tailWord_106787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106787).length < 2 ^ (prefixWord ++ tailWord_106787).sum := by decide
  have hdescent : baseEnd_106787 < baseStart_106787 := by decide
  rcases family_descends (prefixWord ++ tailWord_106787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106830 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_106830 : Nat := 118140960795 + 106830 * 2 ^ 59
def prefixEnd_106830 : Nat := 4983230072969 + 3 ^ 40 * 106830 * 2
def baseEnd_106830 : Nat := 36570092213281507222469

theorem tailTrace_106830 : CollatzResearch.WordTrace tailWord_106830 prefixEnd_106830 36570092213281507222469 := by
  unfold tailWord_106830
  simp only [CollatzResearch.WordTrace]
  refine ⟨487051275372578744567743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2597606801987086637694629 487051275372578744567743)
  ·
    refine ⟨730576913058868116851615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 487051275372578744567743 730576913058868116851615)
    ·
      refine ⟨1095865369588302175277423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 730576913058868116851615 1095865369588302175277423)
      ·
        refine ⟨1643798054382453262916135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095865369588302175277423 1643798054382453262916135)
        ·
          refine ⟨2465697081573679894374203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643798054382453262916135 2465697081573679894374203)
          ·
            refine ⟨3698545622360519841561305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465697081573679894374203 3698545622360519841561305)
            ·
              refine ⟨2773909216770389881170979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3698545622360519841561305 2773909216770389881170979)
              ·
                refine ⟨4160863825155584821756469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2773909216770389881170979 4160863825155584821756469)
                ·
                  refine ⟨390080983608336077039669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4160863825155584821756469 390080983608336077039669)
                  ·
                    refine ⟨36570092213281507222469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 390080983608336077039669 36570092213281507222469)
                    ·
                      rfl

theorem cell22_106830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_106830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106830 prefixEnd_106830 := by exact prefixLift 106830
  have htrace : WordTrace (prefixWord ++ tailWord_106830) baseStart_106830 baseEnd_106830 := by
    simpa [prefixWord, tailWord_106830, baseEnd_106830] using wordTrace_append hprefix tailTrace_106830
  have hstable : (prefixWord ++ tailWord_106830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106830).length < 2 ^ (prefixWord ++ tailWord_106830).sum := by decide
  have hdescent : baseEnd_106830 < baseStart_106830 := by decide
  rcases family_descends (prefixWord ++ tailWord_106830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106832 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 6]
def baseStart_106832 : Nat := 118140960795 + 106832 * 2 ^ 59
def prefixEnd_106832 : Nat := 4983230072969 + 3 ^ 40 * 106832 * 2
def baseEnd_106832 : Nat := 12190258951384722890821

theorem tailTrace_106832 : CollatzResearch.WordTrace tailWord_106832 prefixEnd_106832 12190258951384722890821 := by
  unfold tailWord_106832
  simp only [CollatzResearch.WordTrace]
  refine ⟨1948241574486692149057375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2597655432648922865409833 1948241574486692149057375)
  ·
    refine ⟨2922362361730038223586063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1948241574486692149057375 2922362361730038223586063)
    ·
      refine ⟨4383543542595057335379095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2922362361730038223586063 4383543542595057335379095)
      ·
        refine ⟨6575315313892586003068643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4383543542595057335379095 6575315313892586003068643)
        ·
          refine ⟨9862972970838879004602965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6575315313892586003068643 9862972970838879004602965)
          ·
            refine ⟨115581714502018113335191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 9862972970838879004602965 115581714502018113335191)
            ·
              refine ⟨173372571753027170002787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115581714502018113335191 173372571753027170002787)
              ·
                refine ⟨260058857629540755004181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173372571753027170002787 260058857629540755004181)
                ·
                  refine ⟨12190258951384722890821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 260058857629540755004181 12190258951384722890821)
                  ·
                    rfl

theorem cell22_106832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 6].length) (baseStart_106832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106832 prefixEnd_106832 := by exact prefixLift 106832
  have htrace : WordTrace (prefixWord ++ tailWord_106832) baseStart_106832 baseEnd_106832 := by
    simpa [prefixWord, tailWord_106832, baseEnd_106832] using wordTrace_append hprefix tailTrace_106832
  have hstable : (prefixWord ++ tailWord_106832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106832).length < 2 ^ (prefixWord ++ tailWord_106832).sum := by decide
  have hdescent : baseEnd_106832 < baseStart_106832 := by decide
  rcases family_descends (prefixWord ++ tailWord_106832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106881 : List Nat := [1, 2, 4, 3, 1, 2, 2, 2, 2, 3]
def baseStart_106881 : Nat := 118140960795 + 106881 * 2 ^ 59
def prefixEnd_106881 : Nat := 4983230072969 + 3 ^ 40 * 106881 * 2
def baseEnd_106881 : Nat := 36587550555534374197313

theorem tailTrace_106881 : CollatzResearch.WordTrace tailWord_106881 prefixEnd_106881 36587550555534374197313 := by
  unfold tailWord_106881
  simp only [CollatzResearch.WordTrace]
  refine ⟨3898270325795865666648497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2598846883863910444432331 3898270325795865666648497)
  ·
    refine ⟨2923702744346899249986373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3898270325795865666648497 2923702744346899249986373)
    ·
      refine ⟨548194264565043609372445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2923702744346899249986373 548194264565043609372445)
      ·
        refine ⟨205572849211891353514667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 548194264565043609372445 205572849211891353514667)
        ·
          refine ⟨308359273817837030272001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205572849211891353514667 308359273817837030272001)
          ·
            refine ⟨231269455363377772704001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308359273817837030272001 231269455363377772704001)
            ·
              refine ⟨173452091522533329528001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231269455363377772704001 173452091522533329528001)
              ·
                refine ⟨130089068641899997146001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173452091522533329528001 130089068641899997146001)
                ·
                  refine ⟨97566801481424997859501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130089068641899997146001 97566801481424997859501)
                  ·
                    refine ⟨36587550555534374197313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97566801481424997859501 36587550555534374197313)
                    ·
                      rfl

theorem cell22_106881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_106881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106881 prefixEnd_106881 := by exact prefixLift 106881
  have htrace : WordTrace (prefixWord ++ tailWord_106881) baseStart_106881 baseEnd_106881 := by
    simpa [prefixWord, tailWord_106881, baseEnd_106881] using wordTrace_append hprefix tailTrace_106881
  have hstable : (prefixWord ++ tailWord_106881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106881).length < 2 ^ (prefixWord ++ tailWord_106881).sum := by decide
  have hdescent : baseEnd_106881 < baseStart_106881 := by decide
  rcases family_descends (prefixWord ++ tailWord_106881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106883 : List Nat := [1, 1, 1, 3, 7, 1, 2, 2, 4]
def baseStart_106883 : Nat := 118140960795 + 106883 * 2 ^ 59
def prefixEnd_106883 : Nat := 4983230072969 + 3 ^ 40 * 106883 * 2
def baseEnd_106883 : Nat := 12196078398802345215769

theorem tailTrace_106883 : CollatzResearch.WordTrace tailWord_106883 prefixEnd_106883 12196078398802345215769 := by
  unfold tailWord_106883
  simp only [CollatzResearch.WordTrace]
  refine ⟨3898343271788620008221303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2598895514525746672147535 3898343271788620008221303)
  ·
    refine ⟨5847514907682930012331955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3898343271788620008221303 5847514907682930012331955)
    ·
      refine ⟨8771272361524395018497933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5847514907682930012331955 8771272361524395018497933)
      ·
        refine ⟨3289227135571648131936725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8771272361524395018497933 3289227135571648131936725)
        ·
          refine ⟨77091260989960503092267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3289227135571648131936725 77091260989960503092267)
          ·
            refine ⟨115636891484940754638401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77091260989960503092267 115636891484940754638401)
            ·
              refine ⟨86727668613705565978801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115636891484940754638401 86727668613705565978801)
              ·
                refine ⟨65045751460279174484101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86727668613705565978801 65045751460279174484101)
                ·
                  refine ⟨12196078398802345215769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65045751460279174484101 12196078398802345215769)
                  ·
                    rfl

theorem cell22_106883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 4].length) (baseStart_106883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106883 prefixEnd_106883 := by exact prefixLift 106883
  have htrace : WordTrace (prefixWord ++ tailWord_106883) baseStart_106883 baseEnd_106883 := by
    simpa [prefixWord, tailWord_106883, baseEnd_106883] using wordTrace_append hprefix tailTrace_106883
  have hstable : (prefixWord ++ tailWord_106883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106883).length < 2 ^ (prefixWord ++ tailWord_106883).sum := by decide
  have hdescent : baseEnd_106883 < baseStart_106883 := by decide
  rcases family_descends (prefixWord ++ tailWord_106883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106894 : List Nat := [4, 1, 1, 4, 1, 3, 1, 7]
def baseStart_106894 : Nat := 118140960795 + 106894 * 2 ^ 59
def prefixEnd_106894 : Nat := 4983230072969 + 3 ^ 40 * 106894 * 2
def baseEnd_106894 : Nat := 4065777857911852624697

theorem tailTrace_106894 : CollatzResearch.WordTrace tailWord_106894 prefixEnd_106894 4065777857911852624697 := by
  unfold tailWord_106894
  simp only [CollatzResearch.WordTrace]
  refine ⟨487343059343596110858967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2599162983165845924581157 487343059343596110858967)
  ·
    refine ⟨731014589015394166288451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 487343059343596110858967 731014589015394166288451)
    ·
      refine ⟨1096521883523091249432677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 731014589015394166288451 1096521883523091249432677)
      ·
        refine ⟨205597853160579609268627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1096521883523091249432677 205597853160579609268627)
        ·
          refine ⟨308396779740869413902941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205597853160579609268627 308396779740869413902941)
          ·
            refine ⟨115648792402826030213603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308396779740869413902941 115648792402826030213603)
            ·
              refine ⟨173473188604239045320405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115648792402826030213603 173473188604239045320405)
              ·
                refine ⟨4065777857911852624697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 173473188604239045320405 4065777857911852624697)
                ·
                  rfl

theorem cell22_106894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_106894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106894 prefixEnd_106894 := by exact prefixLift 106894
  have htrace : WordTrace (prefixWord ++ tailWord_106894) baseStart_106894 baseEnd_106894 := by
    simpa [prefixWord, tailWord_106894, baseEnd_106894] using wordTrace_append hprefix tailTrace_106894
  have hstable : (prefixWord ++ tailWord_106894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106894).length < 2 ^ (prefixWord ++ tailWord_106894).sum := by decide
  have hdescent : baseEnd_106894 < baseStart_106894 := by decide
  rcases family_descends (prefixWord ++ tailWord_106894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106913 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 2, 4]
def baseStart_106913 : Nat := 118140960795 + 106913 * 2 ^ 59
def prefixEnd_106913 : Nat := 4983230072969 + 3 ^ 40 * 106913 * 2
def baseEnd_106913 : Nat := 36598504809496957397215

theorem tailTrace_106913 : CollatzResearch.WordTrace tailWord_106913 prefixEnd_106913 36598504809496957397215 := by
  unfold tailWord_106913
  simp only [CollatzResearch.WordTrace]
  refine ⟨3899437461679935131813393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2599624974453290087875595 3899437461679935131813393)
  ·
    refine ⟨2924578096259951348860045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3899437461679935131813393 2924578096259951348860045)
    ·
      refine ⟨1096716786097481755822517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2924578096259951348860045 1096716786097481755822517)
      ·
        refine ⟨102817198696638914608361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1096716786097481755822517 102817198696638914608361)
        ·
          refine ⟨77112899022479185956271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102817198696638914608361 77112899022479185956271)
          ·
            refine ⟨115669348533718778934407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77112899022479185956271 115669348533718778934407)
            ·
              refine ⟨173504022800578168401611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115669348533718778934407 173504022800578168401611)
              ·
                refine ⟨260256034200867252602417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173504022800578168401611 260256034200867252602417)
                ·
                  refine ⟨195192025650650439451813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260256034200867252602417 195192025650650439451813)
                  ·
                    refine ⟨36598504809496957397215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195192025650650439451813 36598504809496957397215)
                    ·
                      rfl

theorem cell22_106913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_106913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106913 prefixEnd_106913 := by exact prefixLift 106913
  have htrace : WordTrace (prefixWord ++ tailWord_106913) baseStart_106913 baseEnd_106913 := by
    simpa [prefixWord, tailWord_106913, baseEnd_106913] using wordTrace_append hprefix tailTrace_106913
  have hstable : (prefixWord ++ tailWord_106913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106913).length < 2 ^ (prefixWord ++ tailWord_106913).sum := by decide
  have hdescent : baseEnd_106913 < baseStart_106913 := by decide
  rcases family_descends (prefixWord ++ tailWord_106913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106932 : List Nat := [2, 5, 2, 2, 2, 1, 1, 2, 2, 3]
def baseStart_106932 : Nat := 118140960795 + 106932 * 2 ^ 59
def prefixEnd_106932 : Nat := 4983230072969 + 3 ^ 40 * 106932 * 2
def baseEnd_106932 : Nat := 36605008897787241172157

theorem tailTrace_106932 : CollatzResearch.WordTrace tailWord_106932 prefixEnd_106932 36605008897787241172157 := by
  unfold tailWord_106932
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950065224305550688377525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2600086965740734251170033 1950065224305550688377525)
  ·
    refine ⟨182818614778645377035393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1950065224305550688377525 182818614778645377035393)
    ·
      refine ⟨137113961083984032776545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182818614778645377035393 137113961083984032776545)
      ·
        refine ⟨102835470812988024582409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137113961083984032776545 102835470812988024582409)
        ·
          refine ⟨77126603109741018436807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102835470812988024582409 77126603109741018436807)
          ·
            refine ⟨115689904664611527655211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77126603109741018436807 115689904664611527655211)
            ·
              refine ⟨173534856996917291482817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115689904664611527655211 173534856996917291482817)
              ·
                refine ⟨130151142747687968612113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173534856996917291482817 130151142747687968612113)
                ·
                  refine ⟨97613357060765976459085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130151142747687968612113 97613357060765976459085)
                  ·
                    refine ⟨36605008897787241172157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97613357060765976459085 36605008897787241172157)
                    ·
                      rfl

theorem cell22_106932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_106932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106932 prefixEnd_106932 := by exact prefixLift 106932
  have htrace : WordTrace (prefixWord ++ tailWord_106932) baseStart_106932 baseEnd_106932 := by
    simpa [prefixWord, tailWord_106932, baseEnd_106932] using wordTrace_append hprefix tailTrace_106932
  have hstable : (prefixWord ++ tailWord_106932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106932).length < 2 ^ (prefixWord ++ tailWord_106932).sum := by decide
  have hdescent : baseEnd_106932 < baseStart_106932 := by decide
  rcases family_descends (prefixWord ++ tailWord_106932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106937 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 2, 5]
def baseStart_106937 : Nat := 118140960795 + 106937 * 2 ^ 59
def prefixEnd_106937 : Nat := 4983230072969 + 3 ^ 40 * 106937 * 2
def baseEnd_106937 : Nat := 36606720499968894797141

theorem tailTrace_106937 : CollatzResearch.WordTrace tailWord_106937 prefixEnd_106937 36606720499968894797141 := by
  unfold tailWord_106937
  simp only [CollatzResearch.WordTrace]
  refine ⟨3900312813592987230687065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2600208542395324820458043 3900312813592987230687065)
  ·
    refine ⟨2925234610194740423015299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3900312813592987230687065 2925234610194740423015299)
    ·
      refine ⟨4387851915292110634522949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2925234610194740423015299 4387851915292110634522949)
      ·
        refine ⟨822722234117270743973053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4387851915292110634522949 822722234117270743973053)
        ·
          refine ⟨308520837793976528989895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 822722234117270743973053 308520837793976528989895)
          ·
            refine ⟨462781256690964793484843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308520837793976528989895 462781256690964793484843)
            ·
              refine ⟨694171885036447190227265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462781256690964793484843 694171885036447190227265)
              ·
                refine ⟨520628913777335392670449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694171885036447190227265 520628913777335392670449)
                ·
                  refine ⟨390471685333001544502837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520628913777335392670449 390471685333001544502837)
                  ·
                    refine ⟨36606720499968894797141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 390471685333001544502837 36606720499968894797141)
                    ·
                      rfl

theorem cell22_106937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_106937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106937 prefixEnd_106937 := by exact prefixLift 106937
  have htrace : WordTrace (prefixWord ++ tailWord_106937) baseStart_106937 baseEnd_106937 := by
    simpa [prefixWord, tailWord_106937, baseEnd_106937] using wordTrace_append hprefix tailTrace_106937
  have hstable : (prefixWord ++ tailWord_106937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106937).length < 2 ^ (prefixWord ++ tailWord_106937).sum := by decide
  have hdescent : baseEnd_106937 < baseStart_106937 := by decide
  rcases family_descends (prefixWord ++ tailWord_106937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106956 : List Nat := [2, 2, 1, 4, 3, 1, 3, 1, 5]
def baseStart_106956 : Nat := 118140960795 + 106956 * 2 ^ 59
def prefixEnd_106956 : Nat := 4983230072969 + 3 ^ 40 * 106956 * 2
def baseEnd_106956 : Nat := 12204408196086392857361

theorem tailTrace_106956 : CollatzResearch.WordTrace tailWord_106956 prefixEnd_106956 12204408196086392857361 := by
  unfold tailWord_106956
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950502900262076737814361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2600670533682768983752481 1950502900262076737814361)
  ·
    refine ⟨1462877175196557553360771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1950502900262076737814361 1462877175196557553360771)
    ·
      refine ⟨2194315762794836330041157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1462877175196557553360771 2194315762794836330041157)
      ·
        refine ⟨411434205524031811882717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2194315762794836330041157 411434205524031811882717)
        ·
          refine ⟨154287827071511929456019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411434205524031811882717 154287827071511929456019)
          ·
            refine ⟨231431740607267894184029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154287827071511929456019 231431740607267894184029)
            ·
              refine ⟨86786902727725460319011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231431740607267894184029 86786902727725460319011)
              ·
                refine ⟨130180354091588190478517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86786902727725460319011 130180354091588190478517)
                ·
                  refine ⟨12204408196086392857361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130180354091588190478517 12204408196086392857361)
                  ·
                    rfl

theorem cell22_106956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_106956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106956 prefixEnd_106956 := by exact prefixLift 106956
  have htrace : WordTrace (prefixWord ++ tailWord_106956) baseStart_106956 baseEnd_106956 := by
    simpa [prefixWord, tailWord_106956, baseEnd_106956] using wordTrace_append hprefix tailTrace_106956
  have hstable : (prefixWord ++ tailWord_106956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106956).length < 2 ^ (prefixWord ++ tailWord_106956).sum := by decide
  have hdescent : baseEnd_106956 < baseStart_106956 := by decide
  rcases family_descends (prefixWord ++ tailWord_106956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_106969 : List Nat := [1, 2, 1, 2, 4, 1, 4, 2, 1, 4]
def baseStart_106969 : Nat := 118140960795 + 106969 * 2 ^ 59
def prefixEnd_106969 : Nat := 4983230072969 + 3 ^ 40 * 106969 * 2
def baseEnd_106969 : Nat := 36617674753931477997043

theorem tailTrace_106969 : CollatzResearch.WordTrace tailWord_106969 prefixEnd_106969 36617674753931477997043 := by
  unfold tailWord_106969
  simp only [CollatzResearch.WordTrace]
  refine ⟨3901479949477056695851961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2600986632984704463901307 3901479949477056695851961)
  ·
    refine ⟨2926109962107792521888971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3901479949477056695851961 2926109962107792521888971)
    ·
      refine ⟨4389164943161688782833457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2926109962107792521888971 4389164943161688782833457)
      ·
        refine ⟨3291873707371266587125093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4389164943161688782833457 3291873707371266587125093)
        ·
          refine ⟨617226320132112485085955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3291873707371266587125093 617226320132112485085955)
          ·
            refine ⟨925839480198168727628933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617226320132112485085955 925839480198168727628933)
            ·
              refine ⟨173594902537156636430425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 925839480198168727628933 173594902537156636430425)
              ·
                refine ⟨130196176902867477322819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173594902537156636430425 130196176902867477322819)
                ·
                  refine ⟨195294265354301215984229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130196176902867477322819 195294265354301215984229)
                  ·
                    refine ⟨36617674753931477997043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195294265354301215984229 36617674753931477997043)
                    ·
                      rfl

theorem cell22_106969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_106969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_106969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_106969 prefixEnd_106969 := by exact prefixLift 106969
  have htrace : WordTrace (prefixWord ++ tailWord_106969) baseStart_106969 baseEnd_106969 := by
    simpa [prefixWord, tailWord_106969, baseEnd_106969] using wordTrace_append hprefix tailTrace_106969
  have hstable : (prefixWord ++ tailWord_106969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_106969).length < 2 ^ (prefixWord ++ tailWord_106969).sum := by decide
  have hdescent : baseEnd_106969 < baseStart_106969 := by decide
  rcases family_descends (prefixWord ++ tailWord_106969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107057 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 7]
def baseStart_107057 : Nat := 118140960795 + 107057 * 2 ^ 59
def prefixEnd_107057 : Nat := 4983230072969 + 3 ^ 40 * 107057 * 2
def baseEnd_107057 : Nat := 12215932984109527265591

theorem tailTrace_107057 : CollatzResearch.WordTrace tailWord_107057 prefixEnd_107057 12215932984109527265591 := by
  unfold tailWord_107057
  simp only [CollatzResearch.WordTrace]
  refine ⟨3904689573158247725055425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2603126382105498483370283 3904689573158247725055425)
  ·
    refine ⟨2928517179868685793791569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3904689573158247725055425 2928517179868685793791569)
    ·
      refine ⟨2196387884901514345343677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2928517179868685793791569 2196387884901514345343677)
      ·
        refine ⟨823645456838067879503879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2196387884901514345343677 823645456838067879503879)
        ·
          refine ⟨1235468185257101819255819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823645456838067879503879 1235468185257101819255819)
          ·
            refine ⟨1853202277885652728883729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235468185257101819255819 1853202277885652728883729)
            ·
              refine ⟨1389901708414239546662797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853202277885652728883729 1389901708414239546662797)
              ·
                refine ⟨521213140655339829998549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1389901708414239546662797 521213140655339829998549)
                ·
                  refine ⟨12215932984109527265591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 521213140655339829998549 12215932984109527265591)
                  ·
                    rfl

theorem cell22_107057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_107057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107057 prefixEnd_107057 := by exact prefixLift 107057
  have htrace : WordTrace (prefixWord ++ tailWord_107057) baseStart_107057 baseEnd_107057 := by
    simpa [prefixWord, tailWord_107057, baseEnd_107057] using wordTrace_append hprefix tailTrace_107057
  have hstable : (prefixWord ++ tailWord_107057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107057).length < 2 ^ (prefixWord ++ tailWord_107057).sum := by decide
  have hdescent : baseEnd_107057 < baseStart_107057 := by decide
  rcases family_descends (prefixWord ++ tailWord_107057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107072 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 1, 7]
def baseStart_107072 : Nat := 118140960795 + 107072 * 2 ^ 59
def prefixEnd_107072 : Nat := 4983230072969 + 3 ^ 40 * 107072 * 2
def baseEnd_107072 : Nat := 36652933758873542671727

theorem tailTrace_107072 : CollatzResearch.WordTrace tailWord_107072 prefixEnd_107072 36652933758873542671727 := by
  unfold tailWord_107072
  simp only [CollatzResearch.WordTrace]
  refine ⟨1952618334051952643425735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2603491112069270191234313 1952618334051952643425735)
  ·
    refine ⟨2928927501077928965138603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1952618334051952643425735 2928927501077928965138603)
    ·
      refine ⟨4393391251616893447707905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2928927501077928965138603 4393391251616893447707905)
      ·
        refine ⟨3295043438712670085780929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4393391251616893447707905 3295043438712670085780929)
        ·
          refine ⟨2471282579034502564335697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3295043438712670085780929 2471282579034502564335697)
          ·
            refine ⟨1853461934275876923251773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2471282579034502564335697 1853461934275876923251773)
            ·
              refine ⟨695048225353453846219415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1853461934275876923251773 695048225353453846219415)
              ·
                refine ⟨1042572338030180769329123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695048225353453846219415 1042572338030180769329123)
                ·
                  refine ⟨1563858507045271153993685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042572338030180769329123 1563858507045271153993685)
                  ·
                    refine ⟨36652933758873542671727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1563858507045271153993685 36652933758873542671727)
                    ·
                      rfl

theorem cell22_107072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_107072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107072 prefixEnd_107072 := by exact prefixLift 107072
  have htrace : WordTrace (prefixWord ++ tailWord_107072) baseStart_107072 baseEnd_107072 := by
    simpa [prefixWord, tailWord_107072, baseEnd_107072] using wordTrace_append hprefix tailTrace_107072
  have hstable : (prefixWord ++ tailWord_107072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107072).length < 2 ^ (prefixWord ++ tailWord_107072).sum := by decide
  have hdescent : baseEnd_107072 < baseStart_107072 := by decide
  rcases family_descends (prefixWord ++ tailWord_107072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107078 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_107078 : Nat := 118140960795 + 107078 * 2 ^ 59
def prefixEnd_107078 : Nat := 4983230072969 + 3 ^ 40 * 107078 * 2
def baseEnd_107078 : Nat := 36654987681491527021709

theorem tailTrace_107078 : CollatzResearch.WordTrace tailWord_107078 prefixEnd_107078 36654987681491527021709 := by
  unfold tailWord_107078
  simp only [CollatzResearch.WordTrace]
  refine ⟨122045484565067759736559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2603637004054778874379925 122045484565067759736559)
  ·
    refine ⟨183068226847601639604839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122045484565067759736559 183068226847601639604839)
    ·
      refine ⟨274602340271402459407259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183068226847601639604839 274602340271402459407259)
      ·
        refine ⟨411903510407103689110889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274602340271402459407259 411903510407103689110889)
        ·
          refine ⟨308927632805327766833167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411903510407103689110889 308927632805327766833167)
          ·
            refine ⟨463391449207991650249751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308927632805327766833167 463391449207991650249751)
            ·
              refine ⟨695087173811987475374627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463391449207991650249751 695087173811987475374627)
              ·
                refine ⟨1042630760717981213061941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695087173811987475374627 1042630760717981213061941)
                ·
                  refine ⟨97746633817310738724557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1042630760717981213061941 97746633817310738724557)
                  ·
                    refine ⟨36654987681491527021709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97746633817310738724557 36654987681491527021709)
                    ·
                      rfl

theorem cell22_107078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_107078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107078 prefixEnd_107078 := by exact prefixLift 107078
  have htrace : WordTrace (prefixWord ++ tailWord_107078) baseStart_107078 baseEnd_107078 := by
    simpa [prefixWord, tailWord_107078, baseEnd_107078] using wordTrace_append hprefix tailTrace_107078
  have hstable : (prefixWord ++ tailWord_107078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107078).length < 2 ^ (prefixWord ++ tailWord_107078).sum := by decide
  have hdescent : baseEnd_107078 < baseStart_107078 := by decide
  rcases family_descends (prefixWord ++ tailWord_107078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107164 : List Nat := [2, 2, 3, 2, 2, 1, 10]
def baseStart_107164 : Nat := 118140960795 + 107164 * 2 ^ 59
def prefixEnd_107164 : Nat := 4983230072969 + 3 ^ 40 * 107164 * 2
def baseEnd_107164 : Nat := 1358682490333924791535

theorem tailTrace_107164 : CollatzResearch.WordTrace tailWord_107164 prefixEnd_107164 1358682490333924791535 := by
  unfold tailWord_107164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1954296091885302499600273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2605728122513736666133697 1954296091885302499600273)
  ·
    refine ⟨1465722068913976874700205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1954296091885302499600273 1465722068913976874700205)
    ·
      refine ⟨549645775842741328012577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1465722068913976874700205 549645775842741328012577)
      ·
        refine ⟨412234331882055996009433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549645775842741328012577 412234331882055996009433)
        ·
          refine ⟨309175748911541997007075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412234331882055996009433 309175748911541997007075)
          ·
            refine ⟨463763623367312995510613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309175748911541997007075 463763623367312995510613)
            ·
              refine ⟨1358682490333924791535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 463763623367312995510613 1358682490333924791535)
              ·
                rfl

theorem cell22_107164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 10].length) (baseStart_107164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107164 prefixEnd_107164 := by exact prefixLift 107164
  have htrace : WordTrace (prefixWord ++ tailWord_107164) baseStart_107164 baseEnd_107164 := by
    simpa [prefixWord, tailWord_107164, baseEnd_107164] using wordTrace_append hprefix tailTrace_107164
  have hstable : (prefixWord ++ tailWord_107164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107164).length < 2 ^ (prefixWord ++ tailWord_107164).sum := by decide
  have hdescent : baseEnd_107164 < baseStart_107164 := by decide
  rcases family_descends (prefixWord ++ tailWord_107164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107181 : List Nat := [1, 5, 2, 1, 1, 3, 2, 7]
def baseStart_107181 : Nat := 118140960795 + 107181 * 2 ^ 59
def prefixEnd_107181 : Nat := 4983230072969 + 3 ^ 40 * 107181 * 2
def baseEnd_107181 : Nat := 4076694076270399077377

theorem tailTrace_107181 : CollatzResearch.WordTrace tailWord_107181 prefixEnd_107181 4076694076270399077377 := by
  unfold tailWord_107181
  simp only [CollatzResearch.WordTrace]
  refine ⟨3909212224709016902569397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2606141483139344601712931 3909212224709016902569397)
  ·
    refine ⟨366488646066470334615881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3909212224709016902569397 366488646066470334615881)
    ·
      refine ⟨274866484549852750961911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 366488646066470334615881 274866484549852750961911)
      ·
        refine ⟨412299726824779126442867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274866484549852750961911 412299726824779126442867)
        ·
          refine ⟨618449590237168689664301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412299726824779126442867 618449590237168689664301)
          ·
            refine ⟨231918596338938258624113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 618449590237168689664301 231918596338938258624113)
            ·
              refine ⟨173938947254203693968085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231918596338938258624113 173938947254203693968085)
              ·
                refine ⟨4076694076270399077377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 173938947254203693968085 4076694076270399077377)
                ·
                  rfl

theorem cell22_107181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 7].length) (baseStart_107181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107181 prefixEnd_107181 := by exact prefixLift 107181
  have htrace : WordTrace (prefixWord ++ tailWord_107181) baseStart_107181 baseEnd_107181 := by
    simpa [prefixWord, tailWord_107181, baseEnd_107181] using wordTrace_append hprefix tailTrace_107181
  have hstable : (prefixWord ++ tailWord_107181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107181).length < 2 ^ (prefixWord ++ tailWord_107181).sum := by decide
  have hdescent : baseEnd_107181 < baseStart_107181 := by decide
  rcases family_descends (prefixWord ++ tailWord_107181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107185 : List Nat := [1, 2, 2, 6, 1, 1, 1, 3, 2, 3]
def baseStart_107185 : Nat := 118140960795 + 107185 * 2 ^ 59
def prefixEnd_107185 : Nat := 4983230072969 + 3 ^ 40 * 107185 * 2
def baseEnd_107185 : Nat := 36691615968178914596381

theorem tailTrace_107185 : CollatzResearch.WordTrace tailWord_107185 prefixEnd_107185 36691615968178914596381 := by
  unfold tailWord_107185
  simp only [CollatzResearch.WordTrace]
  refine ⟨3909358116694525585715009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2606238744463017057143339 3909358116694525585715009)
  ·
    refine ⟨2932018587520894189286257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3909358116694525585715009 2932018587520894189286257)
    ·
      refine ⟨2199013940640670641964693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2932018587520894189286257 2199013940640670641964693)
      ·
        refine ⟨103078778467531436342095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2199013940640670641964693 103078778467531436342095)
        ·
          refine ⟨154618167701297154513143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103078778467531436342095 154618167701297154513143)
          ·
            refine ⟨231927251551945731769715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154618167701297154513143 231927251551945731769715)
            ·
              refine ⟨347890877327918597654573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231927251551945731769715 347890877327918597654573)
              ·
                refine ⟨130459078997969474120465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347890877327918597654573 130459078997969474120465)
                ·
                  refine ⟨97844309248477105590349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130459078997969474120465 97844309248477105590349)
                  ·
                    refine ⟨36691615968178914596381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97844309248477105590349 36691615968178914596381)
                    ·
                      rfl

theorem cell22_107185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_107185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107185 prefixEnd_107185 := by exact prefixLift 107185
  have htrace : WordTrace (prefixWord ++ tailWord_107185) baseStart_107185 baseEnd_107185 := by
    simpa [prefixWord, tailWord_107185, baseEnd_107185] using wordTrace_append hprefix tailTrace_107185
  have hstable : (prefixWord ++ tailWord_107185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107185).length < 2 ^ (prefixWord ++ tailWord_107185).sum := by decide
  have hdescent : baseEnd_107185 < baseStart_107185 := by decide
  rcases family_descends (prefixWord ++ tailWord_107185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107196 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 5, 3]
def baseStart_107196 : Nat := 118140960795 + 107196 * 2 ^ 59
def prefixEnd_107196 : Nat := 4983230072969 + 3 ^ 40 * 107196 * 2
def baseEnd_107196 : Nat := 36695381492978552571347

theorem tailTrace_107196 : CollatzResearch.WordTrace tailWord_107196 prefixEnd_107196 36695381492978552571347 := by
  unfold tailWord_107196
  simp only [CollatzResearch.WordTrace]
  refine ⟨1954879659827337232182721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2606506213103116309576961 1954879659827337232182721)
  ·
    refine ⟨1466159744870502924137041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1954879659827337232182721 1466159744870502924137041)
    ·
      refine ⟨1099619808652877193102781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1466159744870502924137041 1099619808652877193102781)
      ·
        refine ⟨412357428244828947413543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1099619808652877193102781 412357428244828947413543)
        ·
          refine ⟨618536142367243421120315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412357428244828947413543 618536142367243421120315)
          ·
            refine ⟨927804213550865131680473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618536142367243421120315 927804213550865131680473)
            ·
              refine ⟨695853160163148848760355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927804213550865131680473 695853160163148848760355)
              ·
                refine ⟨1043779740244723273140533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695853160163148848760355 1043779740244723273140533)
                ·
                  refine ⟨97854350647942806856925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1043779740244723273140533 97854350647942806856925)
                  ·
                    refine ⟨36695381492978552571347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97854350647942806856925 36695381492978552571347)
                    ·
                      rfl

theorem cell22_107196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_107196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107196 prefixEnd_107196 := by exact prefixLift 107196
  have htrace : WordTrace (prefixWord ++ tailWord_107196) baseStart_107196 baseEnd_107196 := by
    simpa [prefixWord, tailWord_107196, baseEnd_107196] using wordTrace_append hprefix tailTrace_107196
  have hstable : (prefixWord ++ tailWord_107196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107196).length < 2 ^ (prefixWord ++ tailWord_107196).sum := by decide
  have hdescent : baseEnd_107196 < baseStart_107196 := by decide
  rcases family_descends (prefixWord ++ tailWord_107196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107226 : List Nat := [3, 1, 1, 2, 2, 2, 4, 2, 5]
def baseStart_107226 : Nat := 118140960795 + 107226 * 2 ^ 59
def prefixEnd_107226 : Nat := 4983230072969 + 3 ^ 40 * 107226 * 2
def baseEnd_107226 : Nat := 12235217035356158107085

theorem tailTrace_107226 : CollatzResearch.WordTrace tailWord_107226 prefixEnd_107226 12235217035356158107085 := by
  unfold tailWord_107226
  simp only [CollatzResearch.WordTrace]
  refine ⟨977713377386497396989383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2607235673030659725305021 977713377386497396989383)
  ·
    refine ⟨1466570066079746095484075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 977713377386497396989383 1466570066079746095484075)
    ·
      refine ⟨2199855099119619143226113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1466570066079746095484075 2199855099119619143226113)
      ·
        refine ⟨1649891324339714357419585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2199855099119619143226113 1649891324339714357419585)
        ·
          refine ⟨1237418493254785768064689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1649891324339714357419585 1237418493254785768064689)
          ·
            refine ⟨928063869941089326048517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1237418493254785768064689 928063869941089326048517)
            ·
              refine ⟨174011975613954248634097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 928063869941089326048517 174011975613954248634097)
              ·
                refine ⟨130508981710465686475573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174011975613954248634097 130508981710465686475573)
                ·
                  refine ⟨12235217035356158107085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130508981710465686475573 12235217035356158107085)
                  ·
                    rfl

theorem cell22_107226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_107226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107226 prefixEnd_107226 := by exact prefixLift 107226
  have htrace : WordTrace (prefixWord ++ tailWord_107226) baseStart_107226 baseEnd_107226 := by
    simpa [prefixWord, tailWord_107226, baseEnd_107226] using wordTrace_append hprefix tailTrace_107226
  have hstable : (prefixWord ++ tailWord_107226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107226).length < 2 ^ (prefixWord ++ tailWord_107226).sum := by decide
  have hdescent : baseEnd_107226 < baseStart_107226 := by decide
  rcases family_descends (prefixWord ++ tailWord_107226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107256 : List Nat := [2, 1, 2, 1, 1, 2, 4, 4, 1, 4]
def baseStart_107256 : Nat := 118140960795 + 107256 * 2 ^ 59
def prefixEnd_107256 : Nat := 4983230072969 + 3 ^ 40 * 107256 * 2
def baseEnd_107256 : Nat := 36715920719158396071163

theorem tailTrace_107256 : CollatzResearch.WordTrace tailWord_107256 prefixEnd_107256 36715920719158396071163 := by
  unfold tailWord_107256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1955973849718652355774811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2607965132958203141033081 1955973849718652355774811)
  ·
    refine ⟨2933960774577978533662217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1955973849718652355774811 2933960774577978533662217)
    ·
      refine ⟨2200470580933483900246663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2933960774577978533662217 2200470580933483900246663)
      ·
        refine ⟨3300705871400225850369995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2200470580933483900246663 3300705871400225850369995)
        ·
          refine ⟨4951058807100338775554993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3300705871400225850369995 4951058807100338775554993)
          ·
            refine ⟨3713294105325254081666245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4951058807100338775554993 3713294105325254081666245)
            ·
              refine ⟨696242644748485140312421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3713294105325254081666245 696242644748485140312421)
              ·
                refine ⟨130545495890340963808579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 696242644748485140312421 130545495890340963808579)
                ·
                  refine ⟨195818243835511445712869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130545495890340963808579 195818243835511445712869)
                  ·
                    refine ⟨36715920719158396071163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195818243835511445712869 36715920719158396071163)
                    ·
                      rfl

theorem cell22_107256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_107256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107256 prefixEnd_107256 := by exact prefixLift 107256
  have htrace : WordTrace (prefixWord ++ tailWord_107256) baseStart_107256 baseEnd_107256 := by
    simpa [prefixWord, tailWord_107256, baseEnd_107256] using wordTrace_append hprefix tailTrace_107256
  have hstable : (prefixWord ++ tailWord_107256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107256).length < 2 ^ (prefixWord ++ tailWord_107256).sum := by decide
  have hdescent : baseEnd_107256 < baseStart_107256 := by decide
  rcases family_descends (prefixWord ++ tailWord_107256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107273 : List Nat := [1, 2, 1, 1, 3, 2, 6, 1, 1, 4]
def baseStart_107273 : Nat := 118140960795 + 107273 * 2 ^ 59
def prefixEnd_107273 : Nat := 4983230072969 + 3 ^ 40 * 107273 * 2
def baseEnd_107273 : Nat := 36721740166576018396111

theorem tailTrace_107273 : CollatzResearch.WordTrace tailWord_107273 prefixEnd_107273 36721740166576018396111 := by
  unfold tailWord_107273
  simp only [CollatzResearch.WordTrace]
  refine ⟨3912567740375716614918473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2608378493583811076612315 3912567740375716614918473)
  ·
    refine ⟨2934425805281787461188855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3912567740375716614918473 2934425805281787461188855)
    ·
      refine ⟨4401638707922681191783283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2934425805281787461188855 4401638707922681191783283)
      ·
        refine ⟨6602458061884021787674925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4401638707922681191783283 6602458061884021787674925)
        ·
          refine ⟨2475921773206508170378097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6602458061884021787674925 2475921773206508170378097)
          ·
            refine ⟨1856941329904881127783573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2475921773206508170378097 1856941329904881127783573)
            ·
              refine ⟨87044124839291302864855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1856941329904881127783573 87044124839291302864855)
              ·
                refine ⟨130566187258936954297283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87044124839291302864855 130566187258936954297283)
                ·
                  refine ⟨195849280888405431445925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130566187258936954297283 195849280888405431445925)
                  ·
                    refine ⟨36721740166576018396111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 195849280888405431445925 36721740166576018396111)
                    ·
                      rfl

theorem cell22_107273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 1, 4].length) (baseStart_107273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107273 prefixEnd_107273 := by exact prefixLift 107273
  have htrace : WordTrace (prefixWord ++ tailWord_107273) baseStart_107273 baseEnd_107273 := by
    simpa [prefixWord, tailWord_107273, baseEnd_107273] using wordTrace_append hprefix tailTrace_107273
  have hstable : (prefixWord ++ tailWord_107273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107273).length < 2 ^ (prefixWord ++ tailWord_107273).sum := by decide
  have hdescent : baseEnd_107273 < baseStart_107273 := by decide
  rcases family_descends (prefixWord ++ tailWord_107273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107299 : List Nat := [1, 1, 1, 4, 2, 1, 1, 11]
def baseStart_107299 : Nat := 118140960795 + 107299 * 2 ^ 59
def prefixEnd_107299 : Nat := 4983230072969 + 3 ^ 40 * 107299 * 2
def baseEnd_107299 : Nat := 4081182277546735249559

theorem tailTrace_107299 : CollatzResearch.WordTrace tailWord_107299 prefixEnd_107299 4081182277546735249559 := by
  unfold tailWord_107299
  simp only [CollatzResearch.WordTrace]
  refine ⟨3913516038281523055364951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2609010692187682036909967 3913516038281523055364951)
  ·
    refine ⟨5870274057422284583047427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3913516038281523055364951 5870274057422284583047427)
    ·
      refine ⟨8805411086133426874571141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5870274057422284583047427 8805411086133426874571141)
      ·
        refine ⟨1651014578650017538982089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8805411086133426874571141 1651014578650017538982089)
        ·
          refine ⟨1238260933987513154236567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1651014578650017538982089 1238260933987513154236567)
          ·
            refine ⟨1857391400981269731354851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238260933987513154236567 1857391400981269731354851)
            ·
              refine ⟨2786087101471904597032277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1857391400981269731354851 2786087101471904597032277)
              ·
                refine ⟨4081182277546735249559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 2786087101471904597032277 4081182277546735249559)
                ·
                  rfl

theorem cell22_107299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 11].length) (baseStart_107299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107299 prefixEnd_107299 := by exact prefixLift 107299
  have htrace : WordTrace (prefixWord ++ tailWord_107299) baseStart_107299 baseEnd_107299 := by
    simpa [prefixWord, tailWord_107299, baseEnd_107299] using wordTrace_append hprefix tailTrace_107299
  have hstable : (prefixWord ++ tailWord_107299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107299).length < 2 ^ (prefixWord ++ tailWord_107299).sum := by decide
  have hdescent : baseEnd_107299 < baseStart_107299 := by decide
  rcases family_descends (prefixWord ++ tailWord_107299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107322 : List Nat := [3, 1, 1, 1, 7, 1, 1, 3, 4]
def baseStart_107322 : Nat := 118140960795 + 107322 * 2 ^ 59
def prefixEnd_107322 : Nat := 4983230072969 + 3 ^ 40 * 107322 * 2
def baseEnd_107322 : Nat := 12246171289318741306987

theorem tailTrace_107322 : CollatzResearch.WordTrace tailWord_107322 prefixEnd_107322 12246171289318741306987 := by
  unfold tailWord_107322
  simp only [CollatzResearch.WordTrace]
  refine ⟨978588729299549495863055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2609569944798798655634813 978588729299549495863055)
  ·
    refine ⟨1467883093949324243794583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 978588729299549495863055 1467883093949324243794583)
    ·
      refine ⟨2201824640923986365691875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1467883093949324243794583 2201824640923986365691875)
      ·
        refine ⟨3302736961385979548537813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2201824640923986365691875 3302736961385979548537813)
        ·
          refine ⟨77407897532483895668855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3302736961385979548537813 77407897532483895668855)
          ·
            refine ⟨116111846298725843503283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77407897532483895668855 116111846298725843503283)
            ·
              refine ⟨174167769448088765254925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116111846298725843503283 174167769448088765254925)
              ·
                refine ⟨65312913543033286970597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174167769448088765254925 65312913543033286970597)
                ·
                  refine ⟨12246171289318741306987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65312913543033286970597 12246171289318741306987)
                  ·
                    rfl

theorem cell22_107322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_107322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107322 prefixEnd_107322 := by exact prefixLift 107322
  have htrace : WordTrace (prefixWord ++ tailWord_107322) baseStart_107322 baseEnd_107322 := by
    simpa [prefixWord, tailWord_107322, baseEnd_107322] using wordTrace_append hprefix tailTrace_107322
  have hstable : (prefixWord ++ tailWord_107322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107322).length < 2 ^ (prefixWord ++ tailWord_107322).sum := by decide
  have hdescent : baseEnd_107322 < baseStart_107322 := by decide
  rcases family_descends (prefixWord ++ tailWord_107322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107346 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_107346 : Nat := 118140960795 + 107346 * 2 ^ 59
def prefixEnd_107346 : Nat := 4983230072969 + 3 ^ 40 * 107346 * 2
def baseEnd_107346 : Nat := 36746729558428161320887

theorem tailTrace_107346 : CollatzResearch.WordTrace tailWord_107346 prefixEnd_107346 36746729558428161320887 := by
  unfold tailWord_107346
  simp only [CollatzResearch.WordTrace]
  refine ⟨978807567277812520581473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2610153512740833388217261 978807567277812520581473)
  ·
    refine ⟨734105675458359390436105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 978807567277812520581473 734105675458359390436105)
    ·
      refine ⟨550579256593769542827079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 734105675458359390436105 550579256593769542827079)
      ·
        refine ⟨825868884890654314240619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 550579256593769542827079 825868884890654314240619)
        ·
          refine ⟨1238803327335981471360929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 825868884890654314240619 1238803327335981471360929)
          ·
            refine ⟨929102495501986103520697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1238803327335981471360929 929102495501986103520697)
            ·
              refine ⟨696826871626489577640523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 929102495501986103520697 696826871626489577640523)
              ·
                refine ⟨1045240307439734366460785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 696826871626489577640523 1045240307439734366460785)
                ·
                  refine ⟨783930230579800774845589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1045240307439734366460785 783930230579800774845589)
                  ·
                    refine ⟨36746729558428161320887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 783930230579800774845589 36746729558428161320887)
                    ·
                      rfl

theorem cell22_107346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_107346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107346 prefixEnd_107346 := by exact prefixLift 107346
  have htrace : WordTrace (prefixWord ++ tailWord_107346) baseStart_107346 baseEnd_107346 := by
    simpa [prefixWord, tailWord_107346, baseEnd_107346] using wordTrace_append hprefix tailTrace_107346
  have hstable : (prefixWord ++ tailWord_107346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107346).length < 2 ^ (prefixWord ++ tailWord_107346).sum := by decide
  have hdescent : baseEnd_107346 < baseStart_107346 := by decide
  rcases family_descends (prefixWord ++ tailWord_107346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107399 : List Nat := [1, 1, 4, 2, 3, 3, 2, 2, 1, 3]
def baseStart_107399 : Nat := 118140960795 + 107399 * 2 ^ 59
def prefixEnd_107399 : Nat := 4983230072969 + 3 ^ 40 * 107399 * 2
def baseEnd_107399 : Nat := 36764872541553689745725

theorem tailTrace_107399 : CollatzResearch.WordTrace tailWord_107399 prefixEnd_107399 36764872541553689745725 := by
  unfold tailWord_107399
  simp only [CollatzResearch.WordTrace]
  refine ⟨3917163337919240134005251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2611442225279493422670167 3917163337919240134005251)
  ·
    refine ⟨5875745006878860201007877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3917163337919240134005251 5875745006878860201007877)
    ·
      refine ⟨1101702188789786287688977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5875745006878860201007877 1101702188789786287688977)
      ·
        refine ⟨826276641592339715766733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1101702188789786287688977 826276641592339715766733)
        ·
          refine ⟨309853740597127393412525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 826276641592339715766733 309853740597127393412525)
          ·
            refine ⟨116195152723922772529697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309853740597127393412525 116195152723922772529697)
            ·
              refine ⟨87146364542942079397273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116195152723922772529697 87146364542942079397273)
              ·
                refine ⟨65359773407206559547955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87146364542942079397273 65359773407206559547955)
                ·
                  refine ⟨98039660110809839321933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65359773407206559547955 98039660110809839321933)
                  ·
                    refine ⟨36764872541553689745725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98039660110809839321933 36764872541553689745725)
                    ·
                      rfl

theorem cell22_107399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_107399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107399 prefixEnd_107399 := by exact prefixLift 107399
  have htrace : WordTrace (prefixWord ++ tailWord_107399) baseStart_107399 baseEnd_107399 := by
    simpa [prefixWord, tailWord_107399, baseEnd_107399] using wordTrace_append hprefix tailTrace_107399
  have hstable : (prefixWord ++ tailWord_107399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107399).length < 2 ^ (prefixWord ++ tailWord_107399).sum := by decide
  have hdescent : baseEnd_107399 < baseStart_107399 := by decide
  rcases family_descends (prefixWord ++ tailWord_107399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107410 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_107410 : Nat := 118140960795 + 107410 * 2 ^ 59
def prefixEnd_107410 : Nat := 4983230072969 + 3 ^ 40 * 107410 * 2
def baseEnd_107410 : Nat := 36768638066353327720691

theorem tailTrace_107410 : CollatzResearch.WordTrace tailWord_107410 prefixEnd_107410 36768638066353327720691 := by
  unfold tailWord_107410
  simp only [CollatzResearch.WordTrace]
  refine ⟨979391135219847253163921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2611709693919592675103789 979391135219847253163921)
  ·
    refine ⟨734543351414885439872941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 979391135219847253163921 734543351414885439872941)
    ·
      refine ⟨275453756780582039952353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 734543351414885439872941 275453756780582039952353)
      ·
        refine ⟨206590317585436529964265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275453756780582039952353 206590317585436529964265)
        ·
          refine ⟨154942738189077397473199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206590317585436529964265 154942738189077397473199)
          ·
            refine ⟨232414107283616096209799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154942738189077397473199 232414107283616096209799)
            ·
              refine ⟨348621160925424144314699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232414107283616096209799 348621160925424144314699)
              ·
                refine ⟨522931741388136216472049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348621160925424144314699 522931741388136216472049)
                ·
                  refine ⟨392198806041102162354037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 522931741388136216472049 392198806041102162354037)
                  ·
                    refine ⟨36768638066353327720691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 392198806041102162354037 36768638066353327720691)
                    ·
                      rfl

theorem cell22_107410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_107410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107410 prefixEnd_107410 := by exact prefixLift 107410
  have htrace : WordTrace (prefixWord ++ tailWord_107410) baseStart_107410 baseEnd_107410 := by
    simpa [prefixWord, tailWord_107410, baseEnd_107410] using wordTrace_append hprefix tailTrace_107410
  have hstable : (prefixWord ++ tailWord_107410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107410).length < 2 ^ (prefixWord ++ tailWord_107410).sum := by decide
  have hdescent : baseEnd_107410 < baseStart_107410 := by decide
  rcases family_descends (prefixWord ++ tailWord_107410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107423 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 6]
def baseStart_107423 : Nat := 118140960795 + 107423 * 2 ^ 59
def prefixEnd_107423 : Nat := 4983230072969 + 3 ^ 40 * 107423 * 2
def baseEnd_107423 : Nat := 12257696077341875715217

theorem tailTrace_107423 : CollatzResearch.WordTrace tailWord_107423 prefixEnd_107423 12257696077341875715217 := by
  unfold tailWord_107423
  simp only [CollatzResearch.WordTrace]
  refine ⟨3918038689832292232878923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2612025793221528155252615 3918038689832292232878923)
  ·
    refine ⟨5877058034748438349318385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3918038689832292232878923 5877058034748438349318385)
    ·
      refine ⟨4407793526061328761988789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5877058034748438349318385 4407793526061328761988789)
      ·
        refine ⟨413230643068249571436449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4407793526061328761988789 413230643068249571436449)
        ·
          refine ⟨309922982301187178577337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413230643068249571436449 309922982301187178577337)
          ·
            refine ⟨232442236725890383933003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309922982301187178577337 232442236725890383933003)
            ·
              refine ⟨348663355088835575899505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232442236725890383933003 348663355088835575899505)
              ·
                refine ⟨261497516316626681924629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348663355088835575899505 261497516316626681924629)
                ·
                  refine ⟨12257696077341875715217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 261497516316626681924629 12257696077341875715217)
                  ·
                    rfl

theorem cell22_107423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 6].length) (baseStart_107423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107423 prefixEnd_107423 := by exact prefixLift 107423
  have htrace : WordTrace (prefixWord ++ tailWord_107423) baseStart_107423 baseEnd_107423 := by
    simpa [prefixWord, tailWord_107423, baseEnd_107423] using wordTrace_append hprefix tailTrace_107423
  have hstable : (prefixWord ++ tailWord_107423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107423).length < 2 ^ (prefixWord ++ tailWord_107423).sum := by decide
  have hdescent : baseEnd_107423 < baseStart_107423 := by decide
  rcases family_descends (prefixWord ++ tailWord_107423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107436 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 1, 6]
def baseStart_107436 : Nat := 118140960795 + 107436 * 2 ^ 59
def prefixEnd_107436 : Nat := 4983230072969 + 3 ^ 40 * 107436 * 2
def baseEnd_107436 : Nat := 36777538397697926570611

theorem tailTrace_107436 : CollatzResearch.WordTrace tailWord_107436 prefixEnd_107436 36777538397697926570611 := by
  unfold tailWord_107436
  simp only [CollatzResearch.WordTrace]
  refine ⟨1959256419392597726551081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2612341892523463635401441 1959256419392597726551081)
  ·
    refine ⟨1469442314544448294913311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1959256419392597726551081 1469442314544448294913311)
    ·
      refine ⟨2204163471816672442369967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1469442314544448294913311 2204163471816672442369967)
      ·
        refine ⟨3306245207725008663554951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2204163471816672442369967 3306245207725008663554951)
        ·
          refine ⟨4959367811587512995332427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3306245207725008663554951 4959367811587512995332427)
          ·
            refine ⟨7439051717381269492998641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4959367811587512995332427 7439051717381269492998641)
            ·
              refine ⟨5579288788035952119748981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7439051717381269492998641 5579288788035952119748981)
              ·
                refine ⟨523058323878370511226467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5579288788035952119748981 523058323878370511226467)
                ·
                  refine ⟨784587485817555766839701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 523058323878370511226467 784587485817555766839701)
                  ·
                    refine ⟨36777538397697926570611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 784587485817555766839701 36777538397697926570611)
                    ·
                      rfl

theorem cell22_107436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_107436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107436 prefixEnd_107436 := by exact prefixLift 107436
  have htrace : WordTrace (prefixWord ++ tailWord_107436) baseStart_107436 baseEnd_107436 := by
    simpa [prefixWord, tailWord_107436, baseEnd_107436] using wordTrace_append hprefix tailTrace_107436
  have hstable : (prefixWord ++ tailWord_107436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107436).length < 2 ^ (prefixWord ++ tailWord_107436).sum := by decide
  have hdescent : baseEnd_107436 < baseStart_107436 := by decide
  rcases family_descends (prefixWord ++ tailWord_107436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107446 : List Nat := [5, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_107446 : Nat := 118140960795 + 107446 * 2 ^ 59
def prefixEnd_107446 : Nat := 4983230072969 + 3 ^ 40 * 107446 * 2
def baseEnd_107446 : Nat := 12260320534020411273527

theorem tailTrace_107446 : CollatzResearch.WordTrace tailWord_107446 prefixEnd_107446 12260320534020411273527 := by
  unfold tailWord_107446
  simp only [CollatzResearch.WordTrace]
  refine ⟨244929848046810447560387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2612585045832644773977461 244929848046810447560387)
  ·
    refine ⟨367394772070215671340581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 244929848046810447560387 367394772070215671340581)
    ·
      refine ⟨68886519763165438376359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 367394772070215671340581 68886519763165438376359)
      ·
        refine ⟨103329779644748157564539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68886519763165438376359 103329779644748157564539)
        ·
          refine ⟨154994669467122236346809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103329779644748157564539 154994669467122236346809)
          ·
            refine ⟨116246002100341677260107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154994669467122236346809 116246002100341677260107)
            ·
              refine ⟨174369003150512515890161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116246002100341677260107 174369003150512515890161)
              ·
                refine ⟨130776752362884386917621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174369003150512515890161 130776752362884386917621)
                ·
                  refine ⟨12260320534020411273527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130776752362884386917621 12260320534020411273527)
                  ·
                    rfl

theorem cell22_107446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_107446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107446 prefixEnd_107446 := by exact prefixLift 107446
  have htrace : WordTrace (prefixWord ++ tailWord_107446) baseStart_107446 baseEnd_107446 := by
    simpa [prefixWord, tailWord_107446, baseEnd_107446] using wordTrace_append hprefix tailTrace_107446
  have hstable : (prefixWord ++ tailWord_107446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107446).length < 2 ^ (prefixWord ++ tailWord_107446).sum := by decide
  have hdescent : baseEnd_107446 < baseStart_107446 := by decide
  rcases family_descends (prefixWord ++ tailWord_107446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107485 : List Nat := [1, 4, 3, 1, 2, 1, 4, 6]
def baseStart_107485 : Nat := 118140960795 + 107485 * 2 ^ 59
def prefixEnd_107485 : Nat := 4983230072969 + 3 ^ 40 * 107485 * 2
def baseEnd_107485 : Nat := 4088256899897570232829

theorem tailTrace_107485 : CollatzResearch.WordTrace tailWord_107485 prefixEnd_107485 4088256899897570232829 := by
  unfold tailWord_107485
  simp only [CollatzResearch.WordTrace]
  refine ⟨3920300015607676821635909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2613533343738451214423939 3920300015607676821635909)
  ·
    refine ⟨735056252926439404056733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3920300015607676821635909 735056252926439404056733)
    ·
      refine ⟨275646094847414776521275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 735056252926439404056733 275646094847414776521275)
      ·
        refine ⟨413469142271122164781913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275646094847414776521275 413469142271122164781913)
        ·
          refine ⟨310101856703341623586435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413469142271122164781913 310101856703341623586435)
          ·
            refine ⟨465152785055012435379653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310101856703341623586435 465152785055012435379653)
            ·
              refine ⟨87216147197814831633685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 465152785055012435379653 87216147197814831633685)
              ·
                refine ⟨4088256899897570232829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87216147197814831633685 4088256899897570232829)
                ·
                  rfl

theorem cell22_107485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 6].length) (baseStart_107485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107485 prefixEnd_107485 := by exact prefixLift 107485
  have htrace : WordTrace (prefixWord ++ tailWord_107485) baseStart_107485 baseEnd_107485 := by
    simpa [prefixWord, tailWord_107485, baseEnd_107485] using wordTrace_append hprefix tailTrace_107485
  have hstable : (prefixWord ++ tailWord_107485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107485).length < 2 ^ (prefixWord ++ tailWord_107485).sum := by decide
  have hdescent : baseEnd_107485 < baseStart_107485 := by decide
  rcases family_descends (prefixWord ++ tailWord_107485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107508 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 6]
def baseStart_107508 : Nat := 118140960795 + 107508 * 2 ^ 59
def prefixEnd_107508 : Nat := 4983230072969 + 3 ^ 40 * 107508 * 2
def baseEnd_107508 : Nat := 12267395156371246256797

theorem tailTrace_107508 : CollatzResearch.WordTrace tailWord_107508 prefixEnd_107508 12267395156371246256797 := by
  unfold tailWord_107508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1960569447262175874861589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2614092596349567833148785 1960569447262175874861589)
  ·
    refine ⟨91901692840414494134137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1960569447262175874861589 91901692840414494134137)
    ·
      refine ⟨68926269630310870600603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91901692840414494134137 68926269630310870600603)
      ·
        refine ⟨103389404445466305900905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68926269630310870600603 103389404445466305900905)
        ·
          refine ⟨77542053334099729425679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103389404445466305900905 77542053334099729425679)
          ·
            refine ⟨116313080001149594138519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77542053334099729425679 116313080001149594138519)
            ·
              refine ⟨174469620001724391207779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116313080001149594138519 174469620001724391207779)
              ·
                refine ⟨261704430002586586811669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174469620001724391207779 261704430002586586811669)
                ·
                  refine ⟨12267395156371246256797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 261704430002586586811669 12267395156371246256797)
                  ·
                    rfl

theorem cell22_107508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_107508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107508 prefixEnd_107508 := by exact prefixLift 107508
  have htrace : WordTrace (prefixWord ++ tailWord_107508) baseStart_107508 baseEnd_107508 := by
    simpa [prefixWord, tailWord_107508, baseEnd_107508] using wordTrace_append hprefix tailTrace_107508
  have hstable : (prefixWord ++ tailWord_107508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107508).length < 2 ^ (prefixWord ++ tailWord_107508).sum := by decide
  have hdescent : baseEnd_107508 < baseStart_107508 := by decide
  rcases family_descends (prefixWord ++ tailWord_107508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107513 : List Nat := [1, 2, 1, 3, 1, 3, 2, 4, 5]
def baseStart_107513 : Nat := 118140960795 + 107513 * 2 ^ 59
def prefixEnd_107513 : Nat := 4983230072969 + 3 ^ 40 * 107513 * 2
def baseEnd_107513 : Nat := 12267965690431797465125

theorem tailTrace_107513 : CollatzResearch.WordTrace tailWord_107513 prefixEnd_107513 12267965690431797465125 := by
  unfold tailWord_107513
  simp only [CollatzResearch.WordTrace]
  refine ⟨3921321259506237603655193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2614214173004158402436795 3921321259506237603655193)
  ·
    refine ⟨2940990944629678202741395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3921321259506237603655193 2940990944629678202741395)
    ·
      refine ⟨4411486416944517304112093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2940990944629678202741395 4411486416944517304112093)
      ·
        refine ⟨1654307406354193989042035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4411486416944517304112093 1654307406354193989042035)
        ·
          refine ⟨2481461109531290983563053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1654307406354193989042035 2481461109531290983563053)
          ·
            refine ⟨930547916074234118836145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2481461109531290983563053 930547916074234118836145)
            ·
              refine ⟨697910937055675589127109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930547916074234118836145 697910937055675589127109)
              ·
                refine ⟨130858300697939172961333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 697910937055675589127109 130858300697939172961333)
                ·
                  refine ⟨12267965690431797465125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130858300697939172961333 12267965690431797465125)
                  ·
                    rfl

theorem cell22_107513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 5].length) (baseStart_107513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107513 prefixEnd_107513 := by exact prefixLift 107513
  have htrace : WordTrace (prefixWord ++ tailWord_107513) baseStart_107513 baseEnd_107513 := by
    simpa [prefixWord, tailWord_107513, baseEnd_107513] using wordTrace_append hprefix tailTrace_107513
  have hstable : (prefixWord ++ tailWord_107513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107513).length < 2 ^ (prefixWord ++ tailWord_107513).sum := by decide
  have hdescent : baseEnd_107513 < baseStart_107513 := by decide
  rcases family_descends (prefixWord ++ tailWord_107513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107530 : List Nat := [3, 1, 2, 2, 3, 2, 1, 3, 5]
def baseStart_107530 : Nat := 118140960795 + 107530 * 2 ^ 59
def prefixEnd_107530 : Nat := 4983230072969 + 3 ^ 40 * 107530 * 2
def baseEnd_107530 : Nat := 12269905506237671573441

theorem tailTrace_107530 : CollatzResearch.WordTrace tailWord_107530 prefixEnd_107530 12269905506237671573441 := by
  unfold tailWord_107530
  simp only [CollatzResearch.WordTrace]
  refine ⟨980485325111162376756011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2614627533629766338016029 980485325111162376756011)
  ·
    refine ⟨1470727987666743565134017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 980485325111162376756011 1470727987666743565134017)
    ·
      refine ⟨1103045990750057673850513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1470727987666743565134017 1103045990750057673850513)
      ·
        refine ⟨827284493062543255387885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1103045990750057673850513 827284493062543255387885)
        ·
          refine ⟨310231684898453720770457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 827284493062543255387885 310231684898453720770457)
          ·
            refine ⟨232673763673840290577843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310231684898453720770457 232673763673840290577843)
            ·
              refine ⟨349010645510760435866765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232673763673840290577843 349010645510760435866765)
              ·
                refine ⟨130878992066535163450037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349010645510760435866765 130878992066535163450037)
                ·
                  refine ⟨12269905506237671573441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130878992066535163450037 12269905506237671573441)
                  ·
                    rfl

theorem cell22_107530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_107530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107530 prefixEnd_107530 := by exact prefixLift 107530
  have htrace : WordTrace (prefixWord ++ tailWord_107530) baseStart_107530 baseEnd_107530 := by
    simpa [prefixWord, tailWord_107530, baseEnd_107530] using wordTrace_append hprefix tailTrace_107530
  have hstable : (prefixWord ++ tailWord_107530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107530).length < 2 ^ (prefixWord ++ tailWord_107530).sum := by decide
  have hdescent : baseEnd_107530 < baseStart_107530 := by decide
  rcases family_descends (prefixWord ++ tailWord_107530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107573 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_107573 : Nat := 118140960795 + 107573 * 2 ^ 59
def prefixEnd_107573 : Nat := 4983230072969 + 3 ^ 40 * 107573 * 2
def baseEnd_107573 : Nat := 36824436297475235895191

theorem tailTrace_107573 : CollatzResearch.WordTrace tailWord_107573 prefixEnd_107573 36824436297475235895191 := by
  unfold tailWord_107573
  simp only [CollatzResearch.WordTrace]
  refine ⟨3923509639288867850839373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2615673092859245233892915 3923509639288867850839373)
  ·
    refine ⟨1471316114733325444064765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3923509639288867850839373 1471316114733325444064765)
    ·
      refine ⟨551743543024997041524287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1471316114733325444064765 551743543024997041524287)
      ·
        refine ⟨827615314537495562286431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551743543024997041524287 827615314537495562286431)
        ·
          refine ⟨1241422971806243343429647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827615314537495562286431 1241422971806243343429647)
          ·
            refine ⟨1862134457709365015144471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241422971806243343429647 1862134457709365015144471)
            ·
              refine ⟨2793201686564047522716707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1862134457709365015144471 2793201686564047522716707)
              ·
                refine ⟨4189802529846071284075061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793201686564047522716707 4189802529846071284075061)
                ·
                  refine ⟨392793987173069182882037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4189802529846071284075061 392793987173069182882037)
                  ·
                    refine ⟨36824436297475235895191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 392793987173069182882037 36824436297475235895191)
                    ·
                      rfl

theorem cell22_107573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_107573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107573 prefixEnd_107573 := by exact prefixLift 107573
  have htrace : WordTrace (prefixWord ++ tailWord_107573) baseStart_107573 baseEnd_107573 := by
    simpa [prefixWord, tailWord_107573, baseEnd_107573] using wordTrace_append hprefix tailTrace_107573
  have hstable : (prefixWord ++ tailWord_107573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107573).length < 2 ^ (prefixWord ++ tailWord_107573).sum := by decide
  have hdescent : baseEnd_107573 < baseStart_107573 := by decide
  rcases family_descends (prefixWord ++ tailWord_107573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107624 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 4, 3]
def baseStart_107624 : Nat := 118140960795 + 107624 * 2 ^ 59
def prefixEnd_107624 : Nat := 4983230072969 + 3 ^ 40 * 107624 * 2
def baseEnd_107624 : Nat := 36841894639728102870035

theorem tailTrace_107624 : CollatzResearch.WordTrace tailWord_107624 prefixEnd_107624 36841894639728102870035 := by
  unfold tailWord_107624
  simp only [CollatzResearch.WordTrace]
  refine ⟨1962684881052051780472963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2616913174736069040630617 1962684881052051780472963)
  ·
    refine ⟨2944027321578077670709445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1962684881052051780472963 2944027321578077670709445)
    ·
      refine ⟨552005122795889563258021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2944027321578077670709445 552005122795889563258021)
      ·
        refine ⟨103500960524229293110879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 552005122795889563258021 103500960524229293110879)
        ·
          refine ⟨155251440786343939666319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103500960524229293110879 155251440786343939666319)
          ·
            refine ⟨232877161179515909499479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155251440786343939666319 232877161179515909499479)
            ·
              refine ⟨349315741769273864249219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232877161179515909499479 349315741769273864249219)
              ·
                refine ⟨523973612653910796373829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349315741769273864249219 523973612653910796373829)
                ·
                  refine ⟨98245052372608274320093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 523973612653910796373829 98245052372608274320093)
                  ·
                    refine ⟨36841894639728102870035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98245052372608274320093 36841894639728102870035)
                    ·
                      rfl

theorem cell22_107624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_107624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107624 prefixEnd_107624 := by exact prefixLift 107624
  have htrace : WordTrace (prefixWord ++ tailWord_107624) baseStart_107624 baseEnd_107624 := by
    simpa [prefixWord, tailWord_107624, baseEnd_107624] using wordTrace_append hprefix tailTrace_107624
  have hstable : (prefixWord ++ tailWord_107624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107624).length < 2 ^ (prefixWord ++ tailWord_107624).sum := by decide
  have hdescent : baseEnd_107624 < baseStart_107624 := by decide
  rcases family_descends (prefixWord ++ tailWord_107624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107633 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 2, 6]
def baseStart_107633 : Nat := 118140960795 + 107633 * 2 ^ 59
def prefixEnd_107633 : Nat := 4983230072969 + 3 ^ 40 * 107633 * 2
def baseEnd_107633 : Nat := 36844975523655079395007

theorem tailTrace_107633 : CollatzResearch.WordTrace tailWord_107633 prefixEnd_107633 36844975523655079395007 := by
  unfold tailWord_107633
  simp only [CollatzResearch.WordTrace]
  refine ⟨3925698019071498098023553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2617132012714332065349035 3925698019071498098023553)
  ·
    refine ⟨2944273514303623573517665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3925698019071498098023553 2944273514303623573517665)
    ·
      refine ⟨2208205135727717680138249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2944273514303623573517665 2208205135727717680138249)
      ·
        refine ⟨1656153851795788260103687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2208205135727717680138249 1656153851795788260103687)
        ·
          refine ⟨2484230777693682390155531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656153851795788260103687 2484230777693682390155531)
          ·
            refine ⟨3726346166540523585233297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484230777693682390155531 3726346166540523585233297)
            ·
              refine ⟨2794759624905392688924973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3726346166540523585233297 2794759624905392688924973)
              ·
                refine ⟨1048034859339522258346865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2794759624905392688924973 1048034859339522258346865)
                ·
                  refine ⟨786026144504641693760149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1048034859339522258346865 786026144504641693760149)
                  ·
                    refine ⟨36844975523655079395007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 786026144504641693760149 36844975523655079395007)
                    ·
                      rfl

theorem cell22_107633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_107633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107633 prefixEnd_107633 := by exact prefixLift 107633
  have htrace : WordTrace (prefixWord ++ tailWord_107633) baseStart_107633 baseEnd_107633 := by
    simpa [prefixWord, tailWord_107633, baseEnd_107633] using wordTrace_append hprefix tailTrace_107633
  have hstable : (prefixWord ++ tailWord_107633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107633).length < 2 ^ (prefixWord ++ tailWord_107633).sum := by decide
  have hdescent : baseEnd_107633 < baseStart_107633 := by decide
  rcases family_descends (prefixWord ++ tailWord_107633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107652 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 3, 3]
def baseStart_107652 : Nat := 118140960795 + 107652 * 2 ^ 59
def prefixEnd_107652 : Nat := 4983230072969 + 3 ^ 40 * 107652 * 2
def baseEnd_107652 : Nat := 36851479611945363169949

theorem tailTrace_107652 : CollatzResearch.WordTrace tailWord_107652 prefixEnd_107652 36851479611945363169949 := by
  unfold tailWord_107652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963195503001332171482605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2617594004001776228643473 1963195503001332171482605)
  ·
    refine ⟨736198313625499564305977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1963195503001332171482605 736198313625499564305977)
    ·
      refine ⟨552148735219124673229483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 736198313625499564305977 552148735219124673229483)
      ·
        refine ⟨828223102828687009844225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 552148735219124673229483 828223102828687009844225)
        ·
          refine ⟨621167327121515257383169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 828223102828687009844225 621167327121515257383169)
          ·
            refine ⟨465875495341136443037377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621167327121515257383169 465875495341136443037377)
            ·
              refine ⟨349406621505852332278033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 465875495341136443037377 349406621505852332278033)
              ·
                refine ⟨262054966129389249208525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349406621505852332278033 262054966129389249208525)
                ·
                  refine ⟨98270612298520968453197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262054966129389249208525 98270612298520968453197)
                  ·
                    refine ⟨36851479611945363169949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98270612298520968453197 36851479611945363169949)
                    ·
                      rfl

theorem cell22_107652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_107652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107652 prefixEnd_107652 := by exact prefixLift 107652
  have htrace : WordTrace (prefixWord ++ tailWord_107652) baseStart_107652 baseEnd_107652 := by
    simpa [prefixWord, tailWord_107652, baseEnd_107652] using wordTrace_append hprefix tailTrace_107652
  have hstable : (prefixWord ++ tailWord_107652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107652).length < 2 ^ (prefixWord ++ tailWord_107652).sum := by decide
  have hdescent : baseEnd_107652 < baseStart_107652 := by decide
  rcases family_descends (prefixWord ++ tailWord_107652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107712 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 3, 4]
def baseStart_107712 : Nat := 118140960795 + 107712 * 2 ^ 59
def prefixEnd_107712 : Nat := 4983230072969 + 3 ^ 40 * 107712 * 2
def baseEnd_107712 : Nat := 36872018838125206669765

theorem tailTrace_107712 : CollatzResearch.WordTrace tailWord_107712 prefixEnd_107712 36872018838125206669765 := by
  unfold tailWord_107712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1964289692892647295074695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2619052923856863060099593 1964289692892647295074695)
  ·
    refine ⟨2946434539338970942612043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1964289692892647295074695 2946434539338970942612043)
    ·
      refine ⟨4419651809008456413918065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2946434539338970942612043 4419651809008456413918065)
      ·
        refine ⟨3314738856756342310438549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4419651809008456413918065 3314738856756342310438549)
        ·
          refine ⟨155378383910453545801807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3314738856756342310438549 155378383910453545801807)
          ·
            refine ⟨233067575865680318702711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155378383910453545801807 233067575865680318702711)
            ·
              refine ⟨349601363798520478054067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233067575865680318702711 349601363798520478054067)
              ·
                refine ⟨524402045697780717081101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349601363798520478054067 524402045697780717081101)
                ·
                  refine ⟨196650767136667768905413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524402045697780717081101 196650767136667768905413)
                  ·
                    refine ⟨36872018838125206669765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 196650767136667768905413 36872018838125206669765)
                    ·
                      rfl

theorem cell22_107712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_107712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107712 prefixEnd_107712 := by exact prefixLift 107712
  have htrace : WordTrace (prefixWord ++ tailWord_107712) baseStart_107712 baseEnd_107712 := by
    simpa [prefixWord, tailWord_107712, baseEnd_107712] using wordTrace_append hprefix tailTrace_107712
  have hstable : (prefixWord ++ tailWord_107712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107712).length < 2 ^ (prefixWord ++ tailWord_107712).sum := by decide
  have hdescent : baseEnd_107712 < baseStart_107712 := by decide
  rcases family_descends (prefixWord ++ tailWord_107712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107744 : List Nat := [2, 1, 1, 3, 1, 4, 4, 2, 4]
def baseStart_107744 : Nat := 118140960795 + 107744 * 2 ^ 59
def prefixEnd_107744 : Nat := 4983230072969 + 3 ^ 40 * 107744 * 2
def baseEnd_107744 : Nat := 12294324364029263289889

theorem tailTrace_107744 : CollatzResearch.WordTrace tailWord_107744 prefixEnd_107744 12294324364029263289889 := by
  unfold tailWord_107744
  simp only [CollatzResearch.WordTrace]
  refine ⟨1964873260834682027657143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2619831014446242703542857 1964873260834682027657143)
  ·
    refine ⟨2947309891252023041485715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1964873260834682027657143 2947309891252023041485715)
    ·
      refine ⟨4420964836878034562228573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2947309891252023041485715 4420964836878034562228573)
      ·
        refine ⟨1657861813829262960835715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4420964836878034562228573 1657861813829262960835715)
        ·
          refine ⟨2486792720743894441253573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657861813829262960835715 2486792720743894441253573)
          ·
            refine ⟨466273635139480207735045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2486792720743894441253573 466273635139480207735045)
            ·
              refine ⟨87426306588652538950321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 466273635139480207735045 87426306588652538950321)
              ·
                refine ⟨65569729941489404212741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87426306588652538950321 65569729941489404212741)
                ·
                  refine ⟨12294324364029263289889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65569729941489404212741 12294324364029263289889)
                  ·
                    rfl

theorem cell22_107744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 4].length) (baseStart_107744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107744 prefixEnd_107744 := by exact prefixLift 107744
  have htrace : WordTrace (prefixWord ++ tailWord_107744) baseStart_107744 baseEnd_107744 := by
    simpa [prefixWord, tailWord_107744, baseEnd_107744] using wordTrace_append hprefix tailTrace_107744
  have hstable : (prefixWord ++ tailWord_107744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107744).length < 2 ^ (prefixWord ++ tailWord_107744).sum := by decide
  have hdescent : baseEnd_107744 < baseStart_107744 := by decide
  rcases family_descends (prefixWord ++ tailWord_107744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107755 : List Nat := [1, 1, 1, 1, 2, 6, 3, 7]
def baseStart_107755 : Nat := 118140960795 + 107755 * 2 ^ 59
def prefixEnd_107755 : Nat := 4983230072969 + 3 ^ 40 * 107755 * 2
def baseEnd_107755 : Nat := 4098526512987491982737

theorem tailTrace_107755 : CollatzResearch.WordTrace tailWord_107755 prefixEnd_107755 4098526512987491982737 := by
  unfold tailWord_107755
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930147724629512933964719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2620098483086341955976479 3930147724629512933964719)
  ·
    refine ⟨5895221586944269400947079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3930147724629512933964719 5895221586944269400947079)
    ·
      refine ⟨8842832380416404101420619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5895221586944269400947079 8842832380416404101420619)
      ·
        refine ⟨13264248570624606152130929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8842832380416404101420619 13264248570624606152130929)
        ·
          refine ⟨9948186427968454614098197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13264248570624606152130929 9948186427968454614098197)
          ·
            refine ⟨466321238811021310035853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9948186427968454614098197 466321238811021310035853)
            ·
              refine ⟨174870464554132991263445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 466321238811021310035853 174870464554132991263445)
              ·
                refine ⟨4098526512987491982737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 174870464554132991263445 4098526512987491982737)
                ·
                  rfl

theorem cell22_107755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 7].length) (baseStart_107755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107755 prefixEnd_107755 := by exact prefixLift 107755
  have htrace : WordTrace (prefixWord ++ tailWord_107755) baseStart_107755 baseEnd_107755 := by
    simpa [prefixWord, tailWord_107755, baseEnd_107755] using wordTrace_append hprefix tailTrace_107755
  have hstable : (prefixWord ++ tailWord_107755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107755).length < 2 ^ (prefixWord ++ tailWord_107755).sum := by decide
  have hdescent : baseEnd_107755 < baseStart_107755 := by decide
  rcases family_descends (prefixWord ++ tailWord_107755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107774 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_107774 : Nat := 118140960795 + 107774 * 2 ^ 59
def prefixEnd_107774 : Nat := 4983230072969 + 3 ^ 40 * 107774 * 2
def baseEnd_107774 : Nat := 36893242705177711619575

theorem tailTrace_107774 : CollatzResearch.WordTrace tailWord_107774 prefixEnd_107774 36893242705177711619575 := by
  unfold tailWord_107774
  simp only [CollatzResearch.WordTrace]
  refine ⟨491355088945084897363297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2620560474373786119270917 491355088945084897363297)
  ·
    refine ⟨368516316708813673022473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 491355088945084897363297 368516316708813673022473)
    ·
      refine ⟨276387237531610254766855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 368516316708813673022473 276387237531610254766855)
      ·
        refine ⟨414580856297415382150283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276387237531610254766855 414580856297415382150283)
        ·
          refine ⟨621871284446123073225425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414580856297415382150283 621871284446123073225425)
          ·
            refine ⟨466403463334592304919069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 621871284446123073225425 466403463334592304919069)
            ·
              refine ⟨174901298750472114344651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 466403463334592304919069 174901298750472114344651)
              ·
                refine ⟨262351948125708171516977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174901298750472114344651 262351948125708171516977)
                ·
                  refine ⟨196763961094281128637733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262351948125708171516977 196763961094281128637733)
                  ·
                    refine ⟨36893242705177711619575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 196763961094281128637733 36893242705177711619575)
                    ·
                      rfl

theorem cell22_107774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_107774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107774 prefixEnd_107774 := by exact prefixLift 107774
  have htrace : WordTrace (prefixWord ++ tailWord_107774) baseStart_107774 baseEnd_107774 := by
    simpa [prefixWord, tailWord_107774, baseEnd_107774] using wordTrace_append hprefix tailTrace_107774
  have hstable : (prefixWord ++ tailWord_107774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107774).length < 2 ^ (prefixWord ++ tailWord_107774).sum := by decide
  have hdescent : baseEnd_107774 < baseStart_107774 := by decide
  rcases family_descends (prefixWord ++ tailWord_107774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107821 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_107821 : Nat := 118140960795 + 107821 * 2 ^ 59
def prefixEnd_107821 : Nat := 4983230072969 + 3 ^ 40 * 107821 * 2
def baseEnd_107821 : Nat := 36909331765685255694431

theorem tailTrace_107821 : CollatzResearch.WordTrace tailWord_107821 prefixEnd_107821 36909331765685255694431 := by
  unfold tailWord_107821
  simp only [CollatzResearch.WordTrace]
  refine ⟨3932554942390406205867317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2621703294926937470578211 3932554942390406205867317)
  ·
    refine ⟨368677025849100581800061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3932554942390406205867317 368677025849100581800061)
    ·
      refine ⟨138253884693412718175023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368677025849100581800061 138253884693412718175023)
      ·
        refine ⟨207380827040119077262535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138253884693412718175023 207380827040119077262535)
        ·
          refine ⟨311071240560178615893803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207380827040119077262535 311071240560178615893803)
          ·
            refine ⟨466606860840267923840705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311071240560178615893803 466606860840267923840705)
            ·
              refine ⟨349955145630200942880529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466606860840267923840705 349955145630200942880529)
              ·
                refine ⟨262466359222650707160397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349955145630200942880529 262466359222650707160397)
                ·
                  refine ⟨98424884708494015185149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262466359222650707160397 98424884708494015185149)
                  ·
                    refine ⟨36909331765685255694431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98424884708494015185149 36909331765685255694431)
                    ·
                      rfl

theorem cell22_107821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_107821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107821 prefixEnd_107821 := by exact prefixLift 107821
  have htrace : WordTrace (prefixWord ++ tailWord_107821) baseStart_107821 baseEnd_107821 := by
    simpa [prefixWord, tailWord_107821, baseEnd_107821] using wordTrace_append hprefix tailTrace_107821
  have hstable : (prefixWord ++ tailWord_107821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107821).length < 2 ^ (prefixWord ++ tailWord_107821).sum := by decide
  have hdescent : baseEnd_107821 < baseStart_107821 := by decide
  rcases family_descends (prefixWord ++ tailWord_107821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107845 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 8]
def baseStart_107845 : Nat := 118140960795 + 107845 * 2 ^ 59
def prefixEnd_107845 : Nat := 4983230072969 + 3 ^ 40 * 107845 * 2
def baseEnd_107845 : Nat := 12305849152052397698119

theorem tailTrace_107845 : CollatzResearch.WordTrace tailWord_107845 prefixEnd_107845 12305849152052397698119 := by
  unfold tailWord_107845
  simp only [CollatzResearch.WordTrace]
  refine ⟨3933430294303458304740989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2622286862868972203160659 3933430294303458304740989)
  ·
    refine ⟨1475036360363796864277871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3933430294303458304740989 1475036360363796864277871)
    ·
      refine ⟨2212554540545695296416807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1475036360363796864277871 2212554540545695296416807)
      ·
        refine ⟨3318831810818542944625211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2212554540545695296416807 3318831810818542944625211)
        ·
          refine ⟨4978247716227814416937817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3318831810818542944625211 4978247716227814416937817)
          ·
            refine ⟨3733685787170860812703363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4978247716227814416937817 3733685787170860812703363)
            ·
              refine ⟨5600528680756291219055045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3733685787170860812703363 5600528680756291219055045)
              ·
                refine ⟨1050099127641804603572821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5600528680756291219055045 1050099127641804603572821)
                ·
                  refine ⟨12305849152052397698119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1050099127641804603572821 12305849152052397698119)
                  ·
                    rfl

theorem cell22_107845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_107845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107845 prefixEnd_107845 := by exact prefixLift 107845
  have htrace : WordTrace (prefixWord ++ tailWord_107845) baseStart_107845 baseEnd_107845 := by
    simpa [prefixWord, tailWord_107845, baseEnd_107845] using wordTrace_append hprefix tailTrace_107845
  have hstable : (prefixWord ++ tailWord_107845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107845).length < 2 ^ (prefixWord ++ tailWord_107845).sum := by decide
  have hdescent : baseEnd_107845 < baseStart_107845 := by decide
  rcases family_descends (prefixWord ++ tailWord_107845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107877 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_107877 : Nat := 118140960795 + 107877 * 2 ^ 59
def prefixEnd_107877 : Nat := 4983230072969 + 3 ^ 40 * 107877 * 2
def baseEnd_107877 : Nat := 36928501710119776294259

theorem tailTrace_107877 : CollatzResearch.WordTrace tailWord_107877 prefixEnd_107877 36928501710119776294259 := by
  unfold tailWord_107877
  simp only [CollatzResearch.WordTrace]
  refine ⟨3934597430187527769905885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2623064953458351846603923 3934597430187527769905885)
  ·
    refine ⟨1475474036320322913714707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3934597430187527769905885 1475474036320322913714707)
    ·
      refine ⟨2213211054480484370572061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1475474036320322913714707 2213211054480484370572061)
      ·
        refine ⟨829954145430181638964523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2213211054480484370572061 829954145430181638964523)
        ·
          refine ⟨1244931218145272458446785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829954145430181638964523 1244931218145272458446785)
          ·
            refine ⟨933698413608954343835089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1244931218145272458446785 933698413608954343835089)
            ·
              refine ⟨700273810206715757876317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 933698413608954343835089 700273810206715757876317)
              ·
                refine ⟨262602678827518409203619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 700273810206715757876317 262602678827518409203619)
                ·
                  refine ⟨393904018241277613805429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 262602678827518409203619 393904018241277613805429)
                  ·
                    refine ⟨36928501710119776294259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 393904018241277613805429 36928501710119776294259)
                    ·
                      rfl

theorem cell22_107877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_107877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107877 prefixEnd_107877 := by exact prefixLift 107877
  have htrace : WordTrace (prefixWord ++ tailWord_107877) baseStart_107877 baseEnd_107877 := by
    simpa [prefixWord, tailWord_107877, baseEnd_107877] using wordTrace_append hprefix tailTrace_107877
  have hstable : (prefixWord ++ tailWord_107877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107877).length < 2 ^ (prefixWord ++ tailWord_107877).sum := by decide
  have hdescent : baseEnd_107877 < baseStart_107877 := by decide
  rcases family_descends (prefixWord ++ tailWord_107877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107911 : List Nat := [1, 1, 4, 2, 2, 3, 2, 2, 2, 3]
def baseStart_107911 : Nat := 118140960795 + 107911 * 2 ^ 59
def prefixEnd_107911 : Nat := 4983230072969 + 3 ^ 40 * 107911 * 2
def baseEnd_107911 : Nat := 36940140604955020944155

theorem tailTrace_107911 : CollatzResearch.WordTrace tailWord_107911 prefixEnd_107911 36940140604955020944155 := by
  unfold tailWord_107911
  simp only [CollatzResearch.WordTrace]
  refine ⟨3935837512064351576643587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2623891674709567717762391 3935837512064351576643587)
  ·
    refine ⟨5903756268096527364965381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3935837512064351576643587 5903756268096527364965381)
    ·
      refine ⟨1106954300268098880931009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5903756268096527364965381 1106954300268098880931009)
      ·
        refine ⟨830215725201074160698257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1106954300268098880931009 830215725201074160698257)
        ·
          refine ⟨622661793900805620523693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830215725201074160698257 622661793900805620523693)
          ·
            refine ⟨233498172712802107696385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 622661793900805620523693 233498172712802107696385)
            ·
              refine ⟨175123629534601580772289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233498172712802107696385 175123629534601580772289)
              ·
                refine ⟨131342722150951185579217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175123629534601580772289 131342722150951185579217)
                ·
                  refine ⟨98507041613213389184413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131342722150951185579217 98507041613213389184413)
                  ·
                    refine ⟨36940140604955020944155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98507041613213389184413 36940140604955020944155)
                    ·
                      rfl

theorem cell22_107911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_107911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107911 prefixEnd_107911 := by exact prefixLift 107911
  have htrace : WordTrace (prefixWord ++ tailWord_107911) baseStart_107911 baseEnd_107911 := by
    simpa [prefixWord, tailWord_107911, baseEnd_107911] using wordTrace_append hprefix tailTrace_107911
  have hstable : (prefixWord ++ tailWord_107911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107911).length < 2 ^ (prefixWord ++ tailWord_107911).sum := by decide
  have hdescent : baseEnd_107911 < baseStart_107911 := by decide
  rcases family_descends (prefixWord ++ tailWord_107911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107913 : List Nat := [1, 2, 1, 1, 7, 2, 2, 2, 4]
def baseStart_107913 : Nat := 118140960795 + 107913 * 2 ^ 59
def prefixEnd_107913 : Nat := 4983230072969 + 3 ^ 40 * 107913 * 2
def baseEnd_107913 : Nat := 12313608415275894131383

theorem tailTrace_107913 : CollatzResearch.WordTrace tailWord_107913 prefixEnd_107913 12313608415275894131383 := by
  unfold tailWord_107913
  simp only [CollatzResearch.WordTrace]
  refine ⟨3935910458057105918216393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2623940305371403945477595 3935910458057105918216393)
  ·
    refine ⟨2951932843542829438662295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3935910458057105918216393 2951932843542829438662295)
    ·
      refine ⟨4427899265314244157993443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2951932843542829438662295 4427899265314244157993443)
      ·
        refine ⟨6641848897971366236990165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4427899265314244157993443 6641848897971366236990165)
        ·
          refine ⟨155668333546203896179457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 6641848897971366236990165 155668333546203896179457)
          ·
            refine ⟨116751250159652922134593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155668333546203896179457 116751250159652922134593)
            ·
              refine ⟨87563437619739691600945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116751250159652922134593 87563437619739691600945)
              ·
                refine ⟨65672578214804768700709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87563437619739691600945 65672578214804768700709)
                ·
                  refine ⟨12313608415275894131383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65672578214804768700709 12313608415275894131383)
                  ·
                    rfl

theorem cell22_107913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 4].length) (baseStart_107913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107913 prefixEnd_107913 := by exact prefixLift 107913
  have htrace : WordTrace (prefixWord ++ tailWord_107913) baseStart_107913 baseEnd_107913 := by
    simpa [prefixWord, tailWord_107913, baseEnd_107913] using wordTrace_append hprefix tailTrace_107913
  have hstable : (prefixWord ++ tailWord_107913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107913).length < 2 ^ (prefixWord ++ tailWord_107913).sum := by decide
  have hdescent : baseEnd_107913 < baseStart_107913 := by decide
  rcases family_descends (prefixWord ++ tailWord_107913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107924 : List Nat := [2, 4, 2, 1, 2, 1, 3, 7]
def baseStart_107924 : Nat := 118140960795 + 107924 * 2 ^ 59
def prefixEnd_107924 : Nat := 4983230072969 + 3 ^ 40 * 107924 * 2
def baseEnd_107924 : Nat := 4104954530069702263235

theorem tailTrace_107924 : CollatzResearch.WordTrace tailWord_107924 prefixEnd_107924 4104954530069702263235 := by
  unfold tailWord_107924
  simp only [CollatzResearch.WordTrace]
  refine ⟨1968155830508627398433413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2624207774011503197911217 1968155830508627398433413)
  ·
    refine ⟨369029218220367637206265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1968155830508627398433413 369029218220367637206265)
    ·
      refine ⟨276771913665275727904699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369029218220367637206265 276771913665275727904699)
      ·
        refine ⟨415157870497913591857049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276771913665275727904699 415157870497913591857049)
        ·
          refine ⟨311368402873435193892787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415157870497913591857049 311368402873435193892787)
          ·
            refine ⟨467052604310152790839181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311368402873435193892787 467052604310152790839181)
            ·
              refine ⟨175144726616307296564693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 467052604310152790839181 175144726616307296564693)
              ·
                refine ⟨4104954530069702263235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 175144726616307296564693 4104954530069702263235)
                ·
                  rfl

theorem cell22_107924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 7].length) (baseStart_107924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107924 prefixEnd_107924 := by exact prefixLift 107924
  have htrace : WordTrace (prefixWord ++ tailWord_107924) baseStart_107924 baseEnd_107924 := by
    simpa [prefixWord, tailWord_107924, baseEnd_107924] using wordTrace_append hprefix tailTrace_107924
  have hstable : (prefixWord ++ tailWord_107924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107924).length < 2 ^ (prefixWord ++ tailWord_107924).sum := by decide
  have hdescent : baseEnd_107924 < baseStart_107924 := by decide
  rcases family_descends (prefixWord ++ tailWord_107924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_107939 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 3, 3]
def baseStart_107939 : Nat := 118140960795 + 107939 * 2 ^ 59
def prefixEnd_107939 : Nat := 4983230072969 + 3 ^ 40 * 107939 * 2
def baseEnd_107939 : Nat := 36949725577172281244069

theorem tailTrace_107939 : CollatzResearch.WordTrace tailWord_107939 prefixEnd_107939 36949725577172281244069 := by
  unfold tailWord_107939
  simp only [CollatzResearch.WordTrace]
  refine ⟨3936858755962912358662871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2624572503975274905775247 3936858755962912358662871)
  ·
    refine ⟨5905288133944368537994307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3936858755962912358662871 5905288133944368537994307)
    ·
      refine ⟨8857932200916552806991461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5905288133944368537994307 8857932200916552806991461)
      ·
        refine ⟨1660862287671853651310899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8857932200916552806991461 1660862287671853651310899)
        ·
          refine ⟨2491293431507780476966349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1660862287671853651310899 2491293431507780476966349)
          ·
            refine ⟨934235036815417678862381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2491293431507780476966349 934235036815417678862381)
            ·
              refine ⟨350338138805781629573393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 934235036815417678862381 350338138805781629573393)
              ·
                refine ⟨262753604104336222180045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350338138805781629573393 262753604104336222180045)
                ·
                  refine ⟨98532601539126083317517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262753604104336222180045 98532601539126083317517)
                  ·
                    refine ⟨36949725577172281244069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98532601539126083317517 36949725577172281244069)
                    ·
                      rfl

theorem cell22_107939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 3, 3].length) (baseStart_107939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_107939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_107939 prefixEnd_107939 := by exact prefixLift 107939
  have htrace : WordTrace (prefixWord ++ tailWord_107939) baseStart_107939 baseEnd_107939 := by
    simpa [prefixWord, tailWord_107939, baseEnd_107939] using wordTrace_append hprefix tailTrace_107939
  have hstable : (prefixWord ++ tailWord_107939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_107939).length < 2 ^ (prefixWord ++ tailWord_107939).sum := by decide
  have hdescent : baseEnd_107939 < baseStart_107939 := by decide
  rcases family_descends (prefixWord ++ tailWord_107939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108061 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 2, 4]
def baseStart_108061 : Nat := 118140960795 + 108061 * 2 ^ 59
def prefixEnd_108061 : Nat := 4983230072969 + 3 ^ 40 * 108061 * 2
def baseEnd_108061 : Nat := 36991488670404629693695

theorem tailTrace_108061 : CollatzResearch.WordTrace tailWord_108061 prefixEnd_108061 36991488670404629693695 := by
  unfold tailWord_108061
  simp only [CollatzResearch.WordTrace]
  refine ⟨3941308461520927194604037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2627538974347284796402691 3941308461520927194604037)
  ·
    refine ⟨738995336535173848988257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3941308461520927194604037 738995336535173848988257)
    ·
      refine ⟨554246502401380386741193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 738995336535173848988257 554246502401380386741193)
      ·
        refine ⟨415684876801035290055895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554246502401380386741193 415684876801035290055895)
        ·
          refine ⟨623527315201552935083843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415684876801035290055895 623527315201552935083843)
          ·
            refine ⟨935290972802329402625765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623527315201552935083843 935290972802329402625765)
            ·
              refine ⟨175367057400436762992331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 935290972802329402625765 175367057400436762992331)
              ·
                refine ⟨263050586100655144488497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175367057400436762992331 263050586100655144488497)
                ·
                  refine ⟨197287939575491358366373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263050586100655144488497 197287939575491358366373)
                  ·
                    refine ⟨36991488670404629693695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 197287939575491358366373 36991488670404629693695)
                    ·
                      rfl

theorem cell22_108061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_108061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108061 prefixEnd_108061 := by exact prefixLift 108061
  have htrace : WordTrace (prefixWord ++ tailWord_108061) baseStart_108061 baseEnd_108061 := by
    simpa [prefixWord, tailWord_108061, baseEnd_108061] using wordTrace_append hprefix tailTrace_108061
  have hstable : (prefixWord ++ tailWord_108061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108061).length < 2 ^ (prefixWord ++ tailWord_108061).sum := by decide
  have hdescent : baseEnd_108061 < baseStart_108061 := by decide
  rcases family_descends (prefixWord ++ tailWord_108061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108089 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 2, 6]
def baseStart_108089 : Nat := 118140960795 + 108089 * 2 ^ 59
def prefixEnd_108089 : Nat := 4983230072969 + 3 ^ 40 * 108089 * 2
def baseEnd_108089 : Nat := 37001073642621889993609

theorem tailTrace_108089 : CollatzResearch.WordTrace tailWord_108089 prefixEnd_108089 37001073642621889993609 := by
  unfold tailWord_108089
  simp only [CollatzResearch.WordTrace]
  refine ⟨3942329705419487976623321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2628219803612991984415547 3942329705419487976623321)
  ·
    refine ⟨2956747279064615982467491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3942329705419487976623321 2956747279064615982467491)
    ·
      refine ⟨4435120918596923973701237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2956747279064615982467491 4435120918596923973701237)
      ·
        refine ⟨415792586118461622534491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4435120918596923973701237 415792586118461622534491)
        ·
          refine ⟨623688879177692433801737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415792586118461622534491 623688879177692433801737)
          ·
            refine ⟨467766659383269325351303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623688879177692433801737 467766659383269325351303)
            ·
              refine ⟨701649989074903988026955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467766659383269325351303 701649989074903988026955)
              ·
                refine ⟨1052474983612355982040433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701649989074903988026955 1052474983612355982040433)
                ·
                  refine ⟨789356237709266986530325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1052474983612355982040433 789356237709266986530325)
                  ·
                    refine ⟨37001073642621889993609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 789356237709266986530325 37001073642621889993609)
                    ·
                      rfl

theorem cell22_108089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_108089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108089 prefixEnd_108089 := by exact prefixLift 108089
  have htrace : WordTrace (prefixWord ++ tailWord_108089) baseStart_108089 baseEnd_108089 := by
    simpa [prefixWord, tailWord_108089, baseEnd_108089] using wordTrace_append hprefix tailTrace_108089
  have hstable : (prefixWord ++ tailWord_108089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108089).length < 2 ^ (prefixWord ++ tailWord_108089).sum := by decide
  have hdescent : baseEnd_108089 < baseStart_108089 := by decide
  rcases family_descends (prefixWord ++ tailWord_108089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108093 : List Nat := [1, 4, 1, 3, 4, 1, 1, 7]
def baseStart_108093 : Nat := 118140960795 + 108093 * 2 ^ 59
def prefixEnd_108093 : Nat := 4983230072969 + 3 ^ 40 * 108093 * 2
def baseEnd_108093 : Nat := 4111382547151912543733

theorem tailTrace_108093 : CollatzResearch.WordTrace tailWord_108093 prefixEnd_108093 4111382547151912543733 := by
  unfold tailWord_108093
  simp only [CollatzResearch.WordTrace]
  refine ⟨3942475597404996659768933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2628317064936664439845955 3942475597404996659768933)
  ·
    refine ⟨739214174513436873706675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3942475597404996659768933 739214174513436873706675)
    ·
      refine ⟨1108821261770155310560013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 739214174513436873706675 1108821261770155310560013)
      ·
        refine ⟨415807973163808241460005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1108821261770155310560013 415807973163808241460005)
        ·
          refine ⟨77963994968214045273751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 415807973163808241460005 77963994968214045273751)
          ·
            refine ⟨116945992452321067910627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77963994968214045273751 116945992452321067910627)
            ·
              refine ⟨175418988678481601865941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116945992452321067910627 175418988678481601865941)
              ·
                refine ⟨4111382547151912543733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 175418988678481601865941 4111382547151912543733)
                ·
                  rfl

theorem cell22_108093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 7].length) (baseStart_108093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108093 prefixEnd_108093 := by exact prefixLift 108093
  have htrace : WordTrace (prefixWord ++ tailWord_108093) baseStart_108093 baseEnd_108093 := by
    simpa [prefixWord, tailWord_108093, baseEnd_108093] using wordTrace_append hprefix tailTrace_108093
  have hstable : (prefixWord ++ tailWord_108093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108093).length < 2 ^ (prefixWord ++ tailWord_108093).sum := by decide
  have hdescent : baseEnd_108093 < baseStart_108093 := by decide
  rcases family_descends (prefixWord ++ tailWord_108093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108136 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 2, 5]
def baseStart_108136 : Nat := 118140960795 + 108136 * 2 ^ 59
def prefixEnd_108136 : Nat := 4983230072969 + 3 ^ 40 * 108136 * 2
def baseEnd_108136 : Nat := 37017162703129434068465

theorem tailTrace_108136 : CollatzResearch.WordTrace tailWord_108136 prefixEnd_108136 37017162703129434068465 := by
  unfold tailWord_108136
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972021968124607501792131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2629362624166143335722841 1972021968124607501792131)
  ·
    refine ⟨2958032952186911252688197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1972021968124607501792131 2958032952186911252688197)
    ·
      refine ⟨554631178535045859879037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2958032952186911252688197 554631178535045859879037)
      ·
        refine ⟨207986691950642197454639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 554631178535045859879037 207986691950642197454639)
        ·
          refine ⟨311980037925963296181959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207986691950642197454639 311980037925963296181959)
          ·
            refine ⟨467970056888944944272939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311980037925963296181959 467970056888944944272939)
            ·
              refine ⟨701955085333417416409409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467970056888944944272939 701955085333417416409409)
              ·
                refine ⟨526466314000063062307057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701955085333417416409409 526466314000063062307057)
                ·
                  refine ⟨394849735500047296730293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526466314000063062307057 394849735500047296730293)
                  ·
                    refine ⟨37017162703129434068465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 394849735500047296730293 37017162703129434068465)
                    ·
                      rfl

theorem cell22_108136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_108136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108136 prefixEnd_108136 := by exact prefixLift 108136
  have htrace : WordTrace (prefixWord ++ tailWord_108136) baseStart_108136 baseEnd_108136 := by
    simpa [prefixWord, tailWord_108136, baseEnd_108136] using wordTrace_append hprefix tailTrace_108136
  have hstable : (prefixWord ++ tailWord_108136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108136).length < 2 ^ (prefixWord ++ tailWord_108136).sum := by decide
  have hdescent : baseEnd_108136 < baseStart_108136 := by decide
  rcases family_descends (prefixWord ++ tailWord_108136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108138 : List Nat := [3, 1, 3, 2, 1, 4, 1, 2, 5]
def baseStart_108138 : Nat := 118140960795 + 108138 * 2 ^ 59
def prefixEnd_108138 : Nat := 4983230072969 + 3 ^ 40 * 108138 * 2
def baseEnd_108138 : Nat := 12339282448000698506153

theorem tailTrace_108138 : CollatzResearch.WordTrace tailWord_108138 prefixEnd_108138 12339282448000698506153 := by
  unfold tailWord_108138
  simp only [CollatzResearch.WordTrace]
  refine ⟨986029220560492336289267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2629411254827979563438045 986029220560492336289267)
  ·
    refine ⟨1479043830840738504433901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 986029220560492336289267 1479043830840738504433901)
    ·
      refine ⟨554641436565276939162713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1479043830840738504433901 554641436565276939162713)
      ·
        refine ⟨415981077423957704372035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 554641436565276939162713 415981077423957704372035)
        ·
          refine ⟨623971616135936556558053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415981077423957704372035 623971616135936556558053)
          ·
            refine ⟨116994678025488104354635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 623971616135936556558053 116994678025488104354635)
            ·
              refine ⟨175492017038232156531953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116994678025488104354635 175492017038232156531953)
              ·
                refine ⟨131619012778674117398965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175492017038232156531953 131619012778674117398965)
                ·
                  refine ⟨12339282448000698506153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131619012778674117398965 12339282448000698506153)
                  ·
                    rfl

theorem cell22_108138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_108138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108138 prefixEnd_108138 := by exact prefixLift 108138
  have htrace : WordTrace (prefixWord ++ tailWord_108138) baseStart_108138 baseEnd_108138 := by
    simpa [prefixWord, tailWord_108138, baseEnd_108138] using wordTrace_append hprefix tailTrace_108138
  have hstable : (prefixWord ++ tailWord_108138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108138).length < 2 ^ (prefixWord ++ tailWord_108138).sum := by decide
  have hdescent : baseEnd_108138 < baseStart_108138 := by decide
  rcases family_descends (prefixWord ++ tailWord_108138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108183 : List Nat := [1, 1, 3, 3, 2, 2, 3, 3, 4]
def baseStart_108183 : Nat := 118140960795 + 108183 * 2 ^ 59
def prefixEnd_108183 : Nat := 4983230072969 + 3 ^ 40 * 108183 * 2
def baseEnd_108183 : Nat := 12344417254545659381107

theorem tailTrace_108183 : CollatzResearch.WordTrace tailWord_108183 prefixEnd_108183 12344417254545659381107 := by
  unfold tailWord_108183
  simp only [CollatzResearch.WordTrace]
  refine ⟨3945758167078942030545203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2630505444719294687030135 3945758167078942030545203)
  ·
    refine ⟨5918637250618413045817805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3945758167078942030545203 5918637250618413045817805)
    ·
      refine ⟨2219488968981904892181677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5918637250618413045817805 2219488968981904892181677)
      ·
        refine ⟨832308363368214334568129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2219488968981904892181677 832308363368214334568129)
        ·
          refine ⟨624231272526160750926097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 832308363368214334568129 624231272526160750926097)
          ·
            refine ⟨468173454394620563194573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 624231272526160750926097 468173454394620563194573)
            ·
              refine ⟨175565045397982711197965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468173454394620563194573 175565045397982711197965)
              ·
                refine ⟨65836892024243516699237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175565045397982711197965 65836892024243516699237)
                ·
                  refine ⟨12344417254545659381107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65836892024243516699237 12344417254545659381107)
                  ·
                    rfl

theorem cell22_108183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 4].length) (baseStart_108183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108183 prefixEnd_108183 := by exact prefixLift 108183
  have htrace : WordTrace (prefixWord ++ tailWord_108183) baseStart_108183 baseEnd_108183 := by
    simpa [prefixWord, tailWord_108183, baseEnd_108183] using wordTrace_append hprefix tailTrace_108183
  have hstable : (prefixWord ++ tailWord_108183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108183).length < 2 ^ (prefixWord ++ tailWord_108183).sum := by decide
  have hdescent : baseEnd_108183 < baseStart_108183 := by decide
  rcases family_descends (prefixWord ++ tailWord_108183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108196 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_108196 : Nat := 118140960795 + 108196 * 2 ^ 59
def prefixEnd_108196 : Nat := 4983230072969 + 3 ^ 40 * 108196 * 2
def baseEnd_108196 : Nat := 37037701929309277568281

theorem tailTrace_108196 : CollatzResearch.WordTrace tailWord_108196 prefixEnd_108196 37037701929309277568281 := by
  unfold tailWord_108196
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973116158015922625384221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2630821544021230167178961 1973116158015922625384221)
  ·
    refine ⟨739918559255970984519083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1973116158015922625384221 739918559255970984519083)
    ·
      refine ⟨1109877838883956476778625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 739918559255970984519083 1109877838883956476778625)
      ·
        refine ⟨832408379162967357583969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1109877838883956476778625 832408379162967357583969)
        ·
          refine ⟨624306284372225518187977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 832408379162967357583969 624306284372225518187977)
          ·
            refine ⟨468229713279169138640983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 624306284372225518187977 468229713279169138640983)
            ·
              refine ⟨702344569918753707961475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468229713279169138640983 702344569918753707961475)
              ·
                refine ⟨1053516854878130561942213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702344569918753707961475 1053516854878130561942213)
                ·
                  refine ⟨197534410289649480364165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1053516854878130561942213 197534410289649480364165)
                  ·
                    refine ⟨37037701929309277568281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 197534410289649480364165 37037701929309277568281)
                    ·
                      rfl

theorem cell22_108196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_108196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108196 prefixEnd_108196 := by exact prefixLift 108196
  have htrace : WordTrace (prefixWord ++ tailWord_108196) baseStart_108196 baseEnd_108196 := by
    simpa [prefixWord, tailWord_108196, baseEnd_108196] using wordTrace_append hprefix tailTrace_108196
  have hstable : (prefixWord ++ tailWord_108196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108196).length < 2 ^ (prefixWord ++ tailWord_108196).sum := by decide
  have hdescent : baseEnd_108196 < baseStart_108196 := by decide
  rcases family_descends (prefixWord ++ tailWord_108196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108215 : List Nat := [1, 1, 3, 1, 5, 1, 4, 1, 2, 3]
def baseStart_108215 : Nat := 118140960795 + 108215 * 2 ^ 59
def prefixEnd_108215 : Nat := 4983230072969 + 3 ^ 40 * 108215 * 2
def baseEnd_108215 : Nat := 37044206017599561343223

theorem tailTrace_108215 : CollatzResearch.WordTrace tailWord_108215 prefixEnd_108215 37044206017599561343223 := by
  unfold tailWord_108215
  simp only [CollatzResearch.WordTrace]
  refine ⟨3946925302963011495710099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2631283535308674330473399 3946925302963011495710099)
  ·
    refine ⟨5920387954444517243565149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3946925302963011495710099 5920387954444517243565149)
    ·
      refine ⟨2220145482916693966336931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5920387954444517243565149 2220145482916693966336931)
      ·
        refine ⟨3330218224375040949505397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2220145482916693966336931 3330218224375040949505397)
        ·
          refine ⟨312207958535160089016131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3330218224375040949505397 312207958535160089016131)
          ·
            refine ⟨468311937802740133524197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312207958535160089016131 468311937802740133524197)
            ·
              refine ⟨87808488338013775035787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 468311937802740133524197 87808488338013775035787)
              ·
                refine ⟨131712732507020662553681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87808488338013775035787 131712732507020662553681)
                ·
                  refine ⟨98784549380265496915261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131712732507020662553681 98784549380265496915261)
                  ·
                    refine ⟨37044206017599561343223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98784549380265496915261 37044206017599561343223)
                    ·
                      rfl

theorem cell22_108215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_108215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108215 prefixEnd_108215 := by exact prefixLift 108215
  have htrace : WordTrace (prefixWord ++ tailWord_108215) baseStart_108215 baseEnd_108215 := by
    simpa [prefixWord, tailWord_108215, baseEnd_108215] using wordTrace_append hprefix tailTrace_108215
  have hstable : (prefixWord ++ tailWord_108215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108215).length < 2 ^ (prefixWord ++ tailWord_108215).sum := by decide
  have hdescent : baseEnd_108215 < baseStart_108215 := by decide
  rcases family_descends (prefixWord ++ tailWord_108215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108239 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 9]
def baseStart_108239 : Nat := 118140960795 + 108239 * 2 ^ 59
def prefixEnd_108239 : Nat := 4983230072969 + 3 ^ 40 * 108239 * 2
def baseEnd_108239 : Nat := 12350807236023832914383

theorem tailTrace_108239 : CollatzResearch.WordTrace tailWord_108239 prefixEnd_108239 12350807236023832914383 := by
  unfold tailWord_108239
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947800654876063594583771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2631867103250709063055847 3947800654876063594583771)
  ·
    refine ⟨5921700982314095391875657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3947800654876063594583771 5921700982314095391875657)
    ·
      refine ⟨4441275736735571543906743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5921700982314095391875657 4441275736735571543906743)
      ·
        refine ⟨6661913605103357315860115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4441275736735571543906743 6661913605103357315860115)
        ·
          refine ⟨9992870407655035973790173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6661913605103357315860115 9992870407655035973790173)
          ·
            refine ⟨3747326402870638490171315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9992870407655035973790173 3747326402870638490171315)
            ·
              refine ⟨5620989604305957735256973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3747326402870638490171315 5620989604305957735256973)
              ·
                refine ⟨2107871101614734150721365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5620989604305957735256973 2107871101614734150721365)
                ·
                  refine ⟨12350807236023832914383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2107871101614734150721365 12350807236023832914383)
                  ·
                    rfl

theorem cell22_108239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 9].length) (baseStart_108239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108239 prefixEnd_108239 := by exact prefixLift 108239
  have htrace : WordTrace (prefixWord ++ tailWord_108239) baseStart_108239 baseEnd_108239 := by
    simpa [prefixWord, tailWord_108239, baseEnd_108239] using wordTrace_append hprefix tailTrace_108239
  have hstable : (prefixWord ++ tailWord_108239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108239).length < 2 ^ (prefixWord ++ tailWord_108239).sum := by decide
  have hdescent : baseEnd_108239 < baseStart_108239 := by decide
  rcases family_descends (prefixWord ++ tailWord_108239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108256 : List Nat := [2, 1, 1, 3, 1, 2, 3, 4, 5]
def baseStart_108256 : Nat := 118140960795 + 108256 * 2 ^ 59
def prefixEnd_108256 : Nat := 4983230072969 + 3 ^ 40 * 108256 * 2
def baseEnd_108256 : Nat := 12352747051829707022699

theorem tailTrace_108256 : CollatzResearch.WordTrace tailWord_108256 prefixEnd_108256 12352747051829707022699 := by
  unfold tailWord_108256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974210347907237748976311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2632280463876316998635081 1974210347907237748976311)
  ·
    refine ⟨2961315521860856623464467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1974210347907237748976311 2961315521860856623464467)
    ·
      refine ⟨4441973282791284935196701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2961315521860856623464467 4441973282791284935196701)
      ·
        refine ⟨1665739981046731850698763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4441973282791284935196701 1665739981046731850698763)
        ·
          refine ⟨2498609971570097776048145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665739981046731850698763 2498609971570097776048145)
          ·
            refine ⟨1873957478677573332036109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2498609971570097776048145 1873957478677573332036109)
            ·
              refine ⟨702734054504089999513541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1873957478677573332036109 702734054504089999513541)
              ·
                refine ⟨131762635219516874908789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 702734054504089999513541 131762635219516874908789)
                ·
                  refine ⟨12352747051829707022699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131762635219516874908789 12352747051829707022699)
                  ·
                    rfl

theorem cell22_108256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 5].length) (baseStart_108256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108256 prefixEnd_108256 := by exact prefixLift 108256
  have htrace : WordTrace (prefixWord ++ tailWord_108256) baseStart_108256 baseEnd_108256 := by
    simpa [prefixWord, tailWord_108256, baseEnd_108256] using wordTrace_append hprefix tailTrace_108256
  have hstable : (prefixWord ++ tailWord_108256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108256).length < 2 ^ (prefixWord ++ tailWord_108256).sum := by decide
  have hdescent : baseEnd_108256 < baseStart_108256 := by decide
  rcases family_descends (prefixWord ++ tailWord_108256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108260 : List Nat := [2, 3, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_108260 : Nat := 118140960795 + 108260 * 2 ^ 59
def prefixEnd_108260 : Nat := 4983230072969 + 3 ^ 40 * 108260 * 2
def baseEnd_108260 : Nat := 37059610437234443968085

theorem tailTrace_108260 : CollatzResearch.WordTrace tailWord_108260 prefixEnd_108260 37059610437234443968085 := by
  unfold tailWord_108260
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974283293899992090549117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2632377725199989454065489 1974283293899992090549117)
  ·
    refine ⟨740356235212497033955919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1974283293899992090549117 740356235212497033955919)
    ·
      refine ⟨1110534352818745550933879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 740356235212497033955919 1110534352818745550933879)
      ·
        refine ⟨1665801529228118326400819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110534352818745550933879 1665801529228118326400819)
        ·
          refine ⟨2498702293842177489601229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665801529228118326400819 2498702293842177489601229)
          ·
            refine ⟨937013360190816558600461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2498702293842177489601229 937013360190816558600461)
            ·
              refine ⟨351380010071556209475173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 937013360190816558600461 351380010071556209475173)
              ·
                refine ⟨65883751888416789276595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 351380010071556209475173 65883751888416789276595)
                ·
                  refine ⟨98825627832625183914893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65883751888416789276595 98825627832625183914893)
                  ·
                    refine ⟨37059610437234443968085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98825627832625183914893 37059610437234443968085)
                    ·
                      rfl

theorem cell22_108260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_108260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108260 prefixEnd_108260 := by exact prefixLift 108260
  have htrace : WordTrace (prefixWord ++ tailWord_108260) baseStart_108260 baseEnd_108260 := by
    simpa [prefixWord, tailWord_108260, baseEnd_108260] using wordTrace_append hprefix tailTrace_108260
  have hstable : (prefixWord ++ tailWord_108260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108260).length < 2 ^ (prefixWord ++ tailWord_108260).sum := by decide
  have hdescent : baseEnd_108260 < baseStart_108260 := by decide
  rcases family_descends (prefixWord ++ tailWord_108260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108271 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 2, 5]
def baseStart_108271 : Nat := 118140960795 + 108271 * 2 ^ 59
def prefixEnd_108271 : Nat := 4983230072969 + 3 ^ 40 * 108271 * 2
def baseEnd_108271 : Nat := 37063375962034081943051

theorem tailTrace_108271 : CollatzResearch.WordTrace tailWord_108271 prefixEnd_108271 37063375962034081943051 := by
  unfold tailWord_108271
  simp only [CollatzResearch.WordTrace]
  refine ⟨3948967790760133059748667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2632645193840088706499111 3948967790760133059748667)
  ·
    refine ⟨5923451686140199589623001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3948967790760133059748667 5923451686140199589623001)
    ·
      refine ⟨4442588764605149692217251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5923451686140199589623001 4442588764605149692217251)
      ·
        refine ⟨6663883146907724538325877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4442588764605149692217251 6663883146907724538325877)
        ·
          refine ⟨624739045022599175468051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6663883146907724538325877 624739045022599175468051)
          ·
            refine ⟨937108567533898763202077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624739045022599175468051 937108567533898763202077)
            ·
              refine ⟨351415712825212036200779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 937108567533898763202077 351415712825212036200779)
              ·
                refine ⟨527123569237818054301169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351415712825212036200779 527123569237818054301169)
                ·
                  refine ⟨395342676928363540725877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527123569237818054301169 395342676928363540725877)
                  ·
                    refine ⟨37063375962034081943051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 395342676928363540725877 37063375962034081943051)
                    ·
                      rfl

theorem cell22_108271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_108271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108271 prefixEnd_108271 := by exact prefixLift 108271
  have htrace : WordTrace (prefixWord ++ tailWord_108271) baseStart_108271 baseEnd_108271 := by
    simpa [prefixWord, tailWord_108271, baseEnd_108271] using wordTrace_append hprefix tailTrace_108271
  have hstable : (prefixWord ++ tailWord_108271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108271).length < 2 ^ (prefixWord ++ tailWord_108271).sum := by decide
  have hdescent : baseEnd_108271 < baseStart_108271 := by decide
  rcases family_descends (prefixWord ++ tailWord_108271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108350 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_108350 : Nat := 118140960795 + 108350 * 2 ^ 59
def prefixEnd_108350 : Nat := 4983230072969 + 3 ^ 40 * 108350 * 2
def baseEnd_108350 : Nat := 37090419276504209217809

theorem tailTrace_108350 : CollatzResearch.WordTrace tailWord_108350 prefixEnd_108350 37090419276504209217809 := by
  unfold tailWord_108350
  simp only [CollatzResearch.WordTrace]
  refine ⟨493981144684241193984313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2634566104982619701249669 493981144684241193984313)
  ·
    refine ⟨370485858513180895488235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 493981144684241193984313 370485858513180895488235)
    ·
      refine ⟨555728787769771343232353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370485858513180895488235 555728787769771343232353)
      ·
        refine ⟨416796590827328507424265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555728787769771343232353 416796590827328507424265)
        ·
          refine ⟨312597443120496380568199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416796590827328507424265 312597443120496380568199)
          ·
            refine ⟨468896164680744570852299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312597443120496380568199 468896164680744570852299)
            ·
              refine ⟨703344247021116856278449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468896164680744570852299 703344247021116856278449)
              ·
                refine ⟨527508185265837642208837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703344247021116856278449 527508185265837642208837)
                ·
                  refine ⟨98907784737344557914157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 527508185265837642208837 98907784737344557914157)
                  ·
                    refine ⟨37090419276504209217809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98907784737344557914157 37090419276504209217809)
                    ·
                      rfl

theorem cell22_108350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_108350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108350 prefixEnd_108350 := by exact prefixLift 108350
  have htrace : WordTrace (prefixWord ++ tailWord_108350) baseStart_108350 baseEnd_108350 := by
    simpa [prefixWord, tailWord_108350, baseEnd_108350] using wordTrace_append hprefix tailTrace_108350
  have hstable : (prefixWord ++ tailWord_108350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108350).length < 2 ^ (prefixWord ++ tailWord_108350).sum := by decide
  have hdescent : baseEnd_108350 < baseStart_108350 := by decide
  rcases family_descends (prefixWord ++ tailWord_108350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108365 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_108365 : Nat := 118140960795 + 108365 * 2 ^ 59
def prefixEnd_108365 : Nat := 4983230072969 + 3 ^ 40 * 108365 * 2
def baseEnd_108365 : Nat := 37095554083049170092763

theorem tailTrace_108365 : CollatzResearch.WordTrace tailWord_108365 prefixEnd_108365 37095554083049170092763 := by
  unfold tailWord_108365
  simp only [CollatzResearch.WordTrace]
  refine ⟨3952396252419587113670549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2634930834946391409113699 3952396252419587113670549)
  ·
    refine ⟨185268574332168145953307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3952396252419587113670549 185268574332168145953307)
    ·
      refine ⟨277902861498252218929961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185268574332168145953307 277902861498252218929961)
      ·
        refine ⟨208427146123689164197471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277902861498252218929961 208427146123689164197471)
        ·
          refine ⟨312640719185533746296207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208427146123689164197471 312640719185533746296207)
          ·
            refine ⟨468961078778300619444311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312640719185533746296207 468961078778300619444311)
            ·
              refine ⟨703441618167450929166467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468961078778300619444311 703441618167450929166467)
              ·
                refine ⟨1055162427251176393749701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703441618167450929166467 1055162427251176393749701)
                ·
                  refine ⟨197842955109595573828069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1055162427251176393749701 197842955109595573828069)
                  ·
                    refine ⟨37095554083049170092763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 197842955109595573828069 37095554083049170092763)
                    ·
                      rfl

theorem cell22_108365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_108365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108365 prefixEnd_108365 := by exact prefixLift 108365
  have htrace : WordTrace (prefixWord ++ tailWord_108365) baseStart_108365 baseEnd_108365 := by
    simpa [prefixWord, tailWord_108365, baseEnd_108365] using wordTrace_append hprefix tailTrace_108365
  have hstable : (prefixWord ++ tailWord_108365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108365).length < 2 ^ (prefixWord ++ tailWord_108365).sum := by decide
  have hdescent : baseEnd_108365 < baseStart_108365 := by decide
  rcases family_descends (prefixWord ++ tailWord_108365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108380 : List Nat := [2, 2, 4, 2, 2, 1, 2, 7]
def baseStart_108380 : Nat := 118140960795 + 108380 * 2 ^ 59
def prefixEnd_108380 : Nat := 4983230072969 + 3 ^ 40 * 108380 * 2
def baseEnd_108380 : Nat := 4122298765510458996413

theorem tailTrace_108380 : CollatzResearch.WordTrace tailWord_108380 prefixEnd_108380 4122298765510458996413 := by
  unfold tailWord_108380
  simp only [CollatzResearch.WordTrace]
  refine ⟨1976471673682622337733297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2635295564910163116977729 1976471673682622337733297)
  ·
    refine ⟨1482353755261966753299973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1976471673682622337733297 1482353755261966753299973)
    ·
      refine ⟨277941329111618766243745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1482353755261966753299973 277941329111618766243745)
      ·
        refine ⟨208455996833714074682809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277941329111618766243745 208455996833714074682809)
        ·
          refine ⟨156341997625285556012107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208455996833714074682809 156341997625285556012107)
          ·
            refine ⟨234512996437928334018161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156341997625285556012107 234512996437928334018161)
            ·
              refine ⟨175884747328446250513621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234512996437928334018161 175884747328446250513621)
              ·
                refine ⟨4122298765510458996413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 175884747328446250513621 4122298765510458996413)
                ·
                  rfl

theorem cell22_108380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 7].length) (baseStart_108380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108380 prefixEnd_108380 := by exact prefixLift 108380
  have htrace : WordTrace (prefixWord ++ tailWord_108380) baseStart_108380 baseEnd_108380 := by
    simpa [prefixWord, tailWord_108380, baseEnd_108380] using wordTrace_append hprefix tailTrace_108380
  have hstable : (prefixWord ++ tailWord_108380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108380).length < 2 ^ (prefixWord ++ tailWord_108380).sum := by decide
  have hdescent : baseEnd_108380 < baseStart_108380 := by decide
  rcases family_descends (prefixWord ++ tailWord_108380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108455 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 3, 4]
def baseStart_108455 : Nat := 118140960795 + 108455 * 2 ^ 59
def prefixEnd_108455 : Nat := 4983230072969 + 3 ^ 40 * 108455 * 2
def baseEnd_108455 : Nat := 37126362922318935342487

theorem tailTrace_108455 : CollatzResearch.WordTrace tailWord_108455 prefixEnd_108455 37126362922318935342487 := by
  unfold tailWord_108455
  simp only [CollatzResearch.WordTrace]
  refine ⟨3955678822093532484446819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2637119214729021656297879 3955678822093532484446819)
  ·
    refine ⟨5933518233140298726670229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3955678822093532484446819 5933518233140298726670229)
    ·
      refine ⟨278133667178451502812667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5933518233140298726670229 278133667178451502812667)
      ·
        refine ⟨417200500767677254219001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278133667178451502812667 417200500767677254219001)
        ·
          refine ⟨312900375575757940664251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417200500767677254219001 312900375575757940664251)
          ·
            refine ⟨469350563363636910996377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312900375575757940664251 469350563363636910996377)
            ·
              refine ⟨352012922522727683247283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469350563363636910996377 352012922522727683247283)
              ·
                refine ⟨528019383784091524870925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352012922522727683247283 528019383784091524870925)
                ·
                  refine ⟨198007268919034321826597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528019383784091524870925 198007268919034321826597)
                  ·
                    refine ⟨37126362922318935342487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198007268919034321826597 37126362922318935342487)
                    ·
                      rfl

theorem cell22_108455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_108455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108455 prefixEnd_108455 := by exact prefixLift 108455
  have htrace : WordTrace (prefixWord ++ tailWord_108455) baseStart_108455 baseEnd_108455 := by
    simpa [prefixWord, tailWord_108455, baseEnd_108455] using wordTrace_append hprefix tailTrace_108455
  have hstable : (prefixWord ++ tailWord_108455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108455).length < 2 ^ (prefixWord ++ tailWord_108455).sum := by decide
  have hdescent : baseEnd_108455 < baseStart_108455 := by decide
  rcases family_descends (prefixWord ++ tailWord_108455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108485 : List Nat := [1, 3, 1, 1, 1, 1, 1, 8, 2, 3]
def baseStart_108485 : Nat := 118140960795 + 108485 * 2 ^ 59
def prefixEnd_108485 : Nat := 4983230072969 + 3 ^ 40 * 108485 * 2
def baseEnd_108485 : Nat := 37136632535408857092395

theorem tailTrace_108485 : CollatzResearch.WordTrace tailWord_108485 prefixEnd_108485 37136632535408857092395 := by
  unfold tailWord_108485
  simp only [CollatzResearch.WordTrace]
  refine ⟨3956773011984847608038909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2637848674656565072025939 3956773011984847608038909)
  ·
    refine ⟨1483789879494317853014591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3956773011984847608038909 1483789879494317853014591)
    ·
      refine ⟨2225684819241476779521887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1483789879494317853014591 2225684819241476779521887)
      ·
        refine ⟨3338527228862215169282831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2225684819241476779521887 3338527228862215169282831)
        ·
          refine ⟨5007790843293322753924247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3338527228862215169282831 5007790843293322753924247)
          ·
            refine ⟨7511686264939984130886371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5007790843293322753924247 7511686264939984130886371)
            ·
              refine ⟨11267529397409976196329557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7511686264939984130886371 11267529397409976196329557)
              ·
                refine ⟨132041360125898158550737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11267529397409976196329557 132041360125898158550737)
                ·
                  refine ⟨99031020094423618913053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132041360125898158550737 99031020094423618913053)
                  ·
                    refine ⟨37136632535408857092395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99031020094423618913053 37136632535408857092395)
                    ·
                      rfl

theorem cell22_108485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 3].length) (baseStart_108485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108485 prefixEnd_108485 := by exact prefixLift 108485
  have htrace : WordTrace (prefixWord ++ tailWord_108485) baseStart_108485 baseEnd_108485 := by
    simpa [prefixWord, tailWord_108485, baseEnd_108485] using wordTrace_append hprefix tailTrace_108485
  have hstable : (prefixWord ++ tailWord_108485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108485).length < 2 ^ (prefixWord ++ tailWord_108485).sum := by decide
  have hdescent : baseEnd_108485 < baseStart_108485 := by decide
  rcases family_descends (prefixWord ++ tailWord_108485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108515 : List Nat := [1, 1, 1, 6, 1, 2, 4, 6]
def baseStart_108515 : Nat := 118140960795 + 108515 * 2 ^ 59
def prefixEnd_108515 : Nat := 4983230072969 + 3 ^ 40 * 108515 * 2
def baseEnd_108515 : Nat := 4127433572055419871367

theorem tailTrace_108515 : CollatzResearch.WordTrace tailWord_108515 prefixEnd_108515 4127433572055419871367 := by
  unfold tailWord_108515
  simp only [CollatzResearch.WordTrace]
  refine ⟨3957867201876162731630999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2638578134584108487753999 3957867201876162731630999)
  ·
    refine ⟨5936800802814244097446499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3957867201876162731630999 5936800802814244097446499)
    ·
      refine ⟨8905201204221366146169749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5936800802814244097446499 8905201204221366146169749)
      ·
        refine ⟨417431306447876538101707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8905201204221366146169749 417431306447876538101707)
        ·
          refine ⟨626146959671814807152561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417431306447876538101707 626146959671814807152561)
          ·
            refine ⟨469610219753861105364421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626146959671814807152561 469610219753861105364421)
            ·
              refine ⟨88051916203848957255829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 469610219753861105364421 88051916203848957255829)
              ·
                refine ⟨4127433572055419871367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88051916203848957255829 4127433572055419871367)
                ·
                  rfl

theorem cell22_108515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 6].length) (baseStart_108515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108515 prefixEnd_108515 := by exact prefixLift 108515
  have htrace : WordTrace (prefixWord ++ tailWord_108515) baseStart_108515 baseEnd_108515 := by
    simpa [prefixWord, tailWord_108515, baseEnd_108515] using wordTrace_append hprefix tailTrace_108515
  have hstable : (prefixWord ++ tailWord_108515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108515).length < 2 ^ (prefixWord ++ tailWord_108515).sum := by decide
  have hdescent : baseEnd_108515 < baseStart_108515 := by decide
  rcases family_descends (prefixWord ++ tailWord_108515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108547 : List Nat := [1, 1, 1, 3, 2, 1, 1, 8, 1, 3]
def baseStart_108547 : Nat := 118140960795 + 108547 * 2 ^ 59
def prefixEnd_108547 : Nat := 4983230072969 + 3 ^ 40 * 108547 * 2
def baseEnd_108547 : Nat := 37157856402461362042205

theorem tailTrace_108547 : CollatzResearch.WordTrace tailWord_108547 prefixEnd_108547 37157856402461362042205 := by
  unfold tailWord_108547
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959034337760232196795895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2639356225173488131197263 3959034337760232196795895)
  ·
    refine ⟨5938551506640348295193843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3959034337760232196795895 5938551506640348295193843)
    ·
      refine ⟨8907827259960522442790765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5938551506640348295193843 8907827259960522442790765)
      ·
        refine ⟨3340435222485195916046537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8907827259960522442790765 3340435222485195916046537)
        ·
          refine ⟨2505326416863896937034903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3340435222485195916046537 2505326416863896937034903)
          ·
            refine ⟨3757989625295845405552355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505326416863896937034903 3757989625295845405552355)
            ·
              refine ⟨5636984437943768108328533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757989625295845405552355 5636984437943768108328533)
              ·
                refine ⟨66058411382153532519475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5636984437943768108328533 66058411382153532519475)
                ·
                  refine ⟨99087617073230298779213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66058411382153532519475 99087617073230298779213)
                  ·
                    refine ⟨37157856402461362042205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99087617073230298779213 37157856402461362042205)
                    ·
                      rfl

theorem cell22_108547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 8, 1, 3].length) (baseStart_108547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108547 prefixEnd_108547 := by exact prefixLift 108547
  have htrace : WordTrace (prefixWord ++ tailWord_108547) baseStart_108547 baseEnd_108547 := by
    simpa [prefixWord, tailWord_108547, baseEnd_108547] using wordTrace_append hprefix tailTrace_108547
  have hstable : (prefixWord ++ tailWord_108547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108547).length < 2 ^ (prefixWord ++ tailWord_108547).sum := by decide
  have hdescent : baseEnd_108547 < baseStart_108547 := by decide
  rcases family_descends (prefixWord ++ tailWord_108547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108588 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 10]
def baseStart_108588 : Nat := 118140960795 + 108588 * 2 ^ 59
def prefixEnd_108588 : Nat := 4983230072969 + 3 ^ 40 * 108588 * 2
def baseEnd_108588 : Nat := 12390630513450307255693

theorem tailTrace_108588 : CollatzResearch.WordTrace tailWord_108588 prefixEnd_108588 12390630513450307255693 := by
  unfold tailWord_108588
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980264865305848099519209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2640353153741130799358945 1980264865305848099519209)
  ·
    refine ⟨1485198648979386074639407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1980264865305848099519209 1485198648979386074639407)
    ·
      refine ⟨2227797973469079111959111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485198648979386074639407 2227797973469079111959111)
      ·
        refine ⟨3341696960203618667938667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2227797973469079111959111 3341696960203618667938667)
        ·
          refine ⟨5012545440305428001908001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3341696960203618667938667 5012545440305428001908001)
          ·
            refine ⟨3759409080229071001431001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5012545440305428001908001 3759409080229071001431001)
            ·
              refine ⟨2819556810171803251073251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3759409080229071001431001 2819556810171803251073251)
              ·
                refine ⟨4229335215257704876609877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2819556810171803251073251 4229335215257704876609877)
                ·
                  refine ⟨12390630513450307255693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 4229335215257704876609877 12390630513450307255693)
                  ·
                    rfl

theorem cell22_108588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_108588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108588 prefixEnd_108588 := by exact prefixLift 108588
  have htrace : WordTrace (prefixWord ++ tailWord_108588) baseStart_108588 baseEnd_108588 := by
    simpa [prefixWord, tailWord_108588, baseEnd_108588] using wordTrace_append hprefix tailTrace_108588
  have hstable : (prefixWord ++ tailWord_108588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108588).length < 2 ^ (prefixWord ++ tailWord_108588).sum := by decide
  have hdescent : baseEnd_108588 < baseStart_108588 := by decide
  rcases family_descends (prefixWord ++ tailWord_108588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108605 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 6]
def baseStart_108605 : Nat := 118140960795 + 108605 * 2 ^ 59
def prefixEnd_108605 : Nat := 4983230072969 + 3 ^ 40 * 108605 * 2
def baseEnd_108605 : Nat := 12392570329256181364009

theorem tailTrace_108605 : CollatzResearch.WordTrace tailWord_108605 prefixEnd_108605 12392570329256181364009 := by
  unfold tailWord_108605
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961149771550108102407269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2640766514366738734938179 3961149771550108102407269)
  ·
    refine ⟨742715582165645269201363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3961149771550108102407269 742715582165645269201363)
    ·
      refine ⟨1114073373248467903802045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742715582165645269201363 1114073373248467903802045)
      ·
        refine ⟨417777514968175463925767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1114073373248467903802045 417777514968175463925767)
        ·
          refine ⟨626666272452263195888651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417777514968175463925767 626666272452263195888651)
          ·
            refine ⟨939999408678394793832977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626666272452263195888651 939999408678394793832977)
            ·
              refine ⟨704999556508796095374733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939999408678394793832977 704999556508796095374733)
              ·
                refine ⟨264374833690798535765525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 704999556508796095374733 264374833690798535765525)
                ·
                  refine ⟨12392570329256181364009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 264374833690798535765525 12392570329256181364009)
                  ·
                    rfl

theorem cell22_108605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_108605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108605 prefixEnd_108605 := by exact prefixLift 108605
  have htrace : WordTrace (prefixWord ++ tailWord_108605) baseStart_108605 baseEnd_108605 := by
    simpa [prefixWord, tailWord_108605, baseEnd_108605] using wordTrace_append hprefix tailTrace_108605
  have hstable : (prefixWord ++ tailWord_108605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108605).length < 2 ^ (prefixWord ++ tailWord_108605).sum := by decide
  have hdescent : baseEnd_108605 < baseStart_108605 := by decide
  rcases family_descends (prefixWord ++ tailWord_108605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108620 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_108620 : Nat := 118140960795 + 108620 * 2 ^ 59
def prefixEnd_108620 : Nat := 4983230072969 + 3 ^ 40 * 108620 * 2
def baseEnd_108620 : Nat := 37182845794313504966981

theorem tailTrace_108620 : CollatzResearch.WordTrace tailWord_108620 prefixEnd_108620 37182845794313504966981 := by
  unfold tailWord_108620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980848433247882832101657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2641131244330510442802209 1980848433247882832101657)
  ·
    refine ⟨1485636324935912124076243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1980848433247882832101657 1485636324935912124076243)
    ·
      refine ⟨2228454487403868186114365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485636324935912124076243 2228454487403868186114365)
      ·
        refine ⟨835670432776450569792887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2228454487403868186114365 835670432776450569792887)
        ·
          refine ⟨1253505649164675854689331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835670432776450569792887 1253505649164675854689331)
          ·
            refine ⟨1880258473747013782033997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253505649164675854689331 1880258473747013782033997)
            ·
              refine ⟨705096927655130168262749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1880258473747013782033997 705096927655130168262749)
              ·
                refine ⟨264411347870673813098531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 705096927655130168262749 264411347870673813098531)
                ·
                  refine ⟨396617021806010719647797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 264411347870673813098531 396617021806010719647797)
                  ·
                    refine ⟨37182845794313504966981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 396617021806010719647797 37182845794313504966981)
                    ·
                      rfl

theorem cell22_108620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_108620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108620 prefixEnd_108620 := by exact prefixLift 108620
  have htrace : WordTrace (prefixWord ++ tailWord_108620) baseStart_108620 baseEnd_108620 := by
    simpa [prefixWord, tailWord_108620, baseEnd_108620] using wordTrace_append hprefix tailTrace_108620
  have hstable : (prefixWord ++ tailWord_108620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108620).length < 2 ^ (prefixWord ++ tailWord_108620).sum := by decide
  have hdescent : baseEnd_108620 < baseStart_108620 := by decide
  rcases family_descends (prefixWord ++ tailWord_108620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108804 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 1, 6]
def baseStart_108804 : Nat := 118140960795 + 108804 * 2 ^ 59
def prefixEnd_108804 : Nat := 4983230072969 + 3 ^ 40 * 108804 * 2
def baseEnd_108804 : Nat := 37245832754598358366417

theorem tailTrace_108804 : CollatzResearch.WordTrace tailWord_108804 prefixEnd_108804 37245832754598358366417 := by
  unfold tailWord_108804
  simp only [CollatzResearch.WordTrace]
  refine ⟨1984203948914582544450733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2645605265219443392600977 1984203948914582544450733)
  ·
    refine ⟨744076480842968454169025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1984203948914582544450733 744076480842968454169025)
    ·
      refine ⟨558057360632226340626769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 744076480842968454169025 558057360632226340626769)
      ·
        refine ⟨418543020474169755470077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558057360632226340626769 418543020474169755470077)
        ·
          refine ⟨156953632677813658301279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418543020474169755470077 156953632677813658301279)
          ·
            refine ⟨235430449016720487451919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156953632677813658301279 235430449016720487451919)
            ·
              refine ⟨353145673525080731177879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235430449016720487451919 353145673525080731177879)
              ·
                refine ⟨529718510287621096766819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353145673525080731177879 529718510287621096766819)
                ·
                  refine ⟨794577765431431645150229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 529718510287621096766819 794577765431431645150229)
                  ·
                    refine ⟨37245832754598358366417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 794577765431431645150229 37245832754598358366417)
                    ·
                      rfl

theorem cell22_108804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_108804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108804 prefixEnd_108804 := by exact prefixLift 108804
  have htrace : WordTrace (prefixWord ++ tailWord_108804) baseStart_108804 baseEnd_108804 := by
    simpa [prefixWord, tailWord_108804, baseEnd_108804] using wordTrace_append hprefix tailTrace_108804
  have hstable : (prefixWord ++ tailWord_108804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108804).length < 2 ^ (prefixWord ++ tailWord_108804).sum := by decide
  have hdescent : baseEnd_108804 < baseStart_108804 := by decide
  rcases family_descends (prefixWord ++ tailWord_108804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108847 : List Nat := [1, 1, 2, 1, 2, 1, 4, 5, 5]
def baseStart_108847 : Nat := 118140960795 + 108847 * 2 ^ 59
def prefixEnd_108847 : Nat := 4983230072969 + 3 ^ 40 * 108847 * 2
def baseEnd_108847 : Nat := 12420184177786859847095

theorem tailTrace_108847 : CollatzResearch.WordTrace tailWord_108847 prefixEnd_108847 12420184177786859847095 := by
  unfold tailWord_108847
  simp only [CollatzResearch.WordTrace]
  refine ⟨3969976236673383432716795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2646650824448922288477863 3969976236673383432716795)
  ·
    refine ⟨5954964355010075149075193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3969976236673383432716795 5954964355010075149075193)
    ·
      refine ⟨4466223266257556361806395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5954964355010075149075193 4466223266257556361806395)
      ·
        refine ⟨6699334899386334542709593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4466223266257556361806395 6699334899386334542709593)
        ·
          refine ⟨5024501174539750907032195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6699334899386334542709593 5024501174539750907032195)
          ·
            refine ⟨7536751761809626360548293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5024501174539750907032195 7536751761809626360548293)
            ·
              refine ⟨1413140955339304942602805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7536751761809626360548293 1413140955339304942602805)
              ·
                refine ⟨132481964563059838369013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1413140955339304942602805 132481964563059838369013)
                ·
                  refine ⟨12420184177786859847095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132481964563059838369013 12420184177786859847095)
                  ·
                    rfl

theorem cell22_108847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 5].length) (baseStart_108847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108847 prefixEnd_108847 := by exact prefixLift 108847
  have htrace : WordTrace (prefixWord ++ tailWord_108847) baseStart_108847 baseEnd_108847 := by
    simpa [prefixWord, tailWord_108847, baseEnd_108847] using wordTrace_append hprefix tailTrace_108847
  have hstable : (prefixWord ++ tailWord_108847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108847).length < 2 ^ (prefixWord ++ tailWord_108847).sum := by decide
  have hdescent : baseEnd_108847 < baseStart_108847 := by decide
  rcases family_descends (prefixWord ++ tailWord_108847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108885 : List Nat := [1, 3, 2, 2, 4, 1, 3, 2, 1, 3]
def baseStart_108885 : Nat := 118140960795 + 108885 * 2 ^ 59
def prefixEnd_108885 : Nat := 4983230072969 + 3 ^ 40 * 108885 * 2
def baseEnd_108885 : Nat := 37273560709941147091169

theorem tailTrace_108885 : CollatzResearch.WordTrace tailWord_108885 prefixEnd_108885 37273560709941147091169 := by
  unfold tailWord_108885
  simp only [CollatzResearch.WordTrace]
  refine ⟨3971362210535715922600109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2647574807023810615066739 3971362210535715922600109)
  ·
    refine ⟨1489260828950893470975041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3971362210535715922600109 1489260828950893470975041)
    ·
      refine ⟨1116945621713170103231281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1489260828950893470975041 1116945621713170103231281)
      ·
        refine ⟨837709216284877577423461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1116945621713170103231281 837709216284877577423461)
        ·
          refine ⟨157070478053414545766899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 837709216284877577423461 157070478053414545766899)
          ·
            refine ⟨235605717080121818650349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157070478053414545766899 235605717080121818650349)
            ·
              refine ⟨88352143905045681993881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235605717080121818650349 88352143905045681993881)
              ·
                refine ⟨66264107928784261495411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88352143905045681993881 66264107928784261495411)
                ·
                  refine ⟨99396161893176392243117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66264107928784261495411 99396161893176392243117)
                  ·
                    refine ⟨37273560709941147091169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99396161893176392243117 37273560709941147091169)
                    ·
                      rfl

theorem cell22_108885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_108885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108885 prefixEnd_108885 := by exact prefixLift 108885
  have htrace : WordTrace (prefixWord ++ tailWord_108885) baseStart_108885 baseEnd_108885 := by
    simpa [prefixWord, tailWord_108885, baseEnd_108885] using wordTrace_append hprefix tailTrace_108885
  have hstable : (prefixWord ++ tailWord_108885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108885).length < 2 ^ (prefixWord ++ tailWord_108885).sum := by decide
  have hdescent : baseEnd_108885 < baseStart_108885 := by decide
  rcases family_descends (prefixWord ++ tailWord_108885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108898 : List Nat := [3, 3, 2, 1, 1, 4, 2, 1, 5]
def baseStart_108898 : Nat := 118140960795 + 108898 * 2 ^ 59
def prefixEnd_108898 : Nat := 4983230072969 + 3 ^ 40 * 108898 * 2
def baseEnd_108898 : Nat := 12426003625204482172043

theorem tailTrace_108898 : CollatzResearch.WordTrace tailWord_108898 prefixEnd_108898 12426003625204482172043 := by
  unfold tailWord_108898
  simp only [CollatzResearch.WordTrace]
  refine ⟨992959089872154785705837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2647890906325746095215565 992959089872154785705837)
  ·
    refine ⟨372359658702058044639689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 992959089872154785705837 372359658702058044639689)
    ·
      refine ⟨279269744026543533479767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372359658702058044639689 279269744026543533479767)
      ·
        refine ⟨418904616039815300219651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279269744026543533479767 418904616039815300219651)
        ·
          refine ⟨628356924059722950329477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418904616039815300219651 628356924059722950329477)
          ·
            refine ⟨117816923261198053186777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 628356924059722950329477 117816923261198053186777)
            ·
              refine ⟨88362692445898539890083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117816923261198053186777 88362692445898539890083)
              ·
                refine ⟨132544038668847809835125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88362692445898539890083 132544038668847809835125)
                ·
                  refine ⟨12426003625204482172043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132544038668847809835125 12426003625204482172043)
                  ·
                    rfl

theorem cell22_108898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_108898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108898 prefixEnd_108898 := by exact prefixLift 108898
  have htrace : WordTrace (prefixWord ++ tailWord_108898) baseStart_108898 baseEnd_108898 := by
    simpa [prefixWord, tailWord_108898, baseEnd_108898] using wordTrace_append hprefix tailTrace_108898
  have hstable : (prefixWord ++ tailWord_108898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108898).length < 2 ^ (prefixWord ++ tailWord_108898).sum := by decide
  have hdescent : baseEnd_108898 < baseStart_108898 := by decide
  rcases family_descends (prefixWord ++ tailWord_108898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108924 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 4, 3]
def baseStart_108924 : Nat := 118140960795 + 108924 * 2 ^ 59
def prefixEnd_108924 : Nat := 4983230072969 + 3 ^ 40 * 108924 * 2
def baseEnd_108924 : Nat := 37286911206958045366049

theorem tailTrace_108924 : CollatzResearch.WordTrace tailWord_108924 prefixEnd_108924 37286911206958045366049 := by
  unfold tailWord_108924
  simp only [CollatzResearch.WordTrace]
  refine ⟨1986392328697212791634913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2648523104929617055513217 1986392328697212791634913)
  ·
    refine ⟨1489794246522909593726185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1986392328697212791634913 1489794246522909593726185)
    ·
      refine ⟨1117345684892182195294639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1489794246522909593726185 1117345684892182195294639)
      ·
        refine ⟨1676018527338273292941959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1117345684892182195294639 1676018527338273292941959)
        ·
          refine ⟨2514027791007409939412939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1676018527338273292941959 2514027791007409939412939)
          ·
            refine ⟨3771041686511114909119409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2514027791007409939412939 3771041686511114909119409)
            ·
              refine ⟨2828281264883336181839557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3771041686511114909119409 2828281264883336181839557)
              ·
                refine ⟨530302737165625534094917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2828281264883336181839557 530302737165625534094917)
                ·
                  refine ⟨99431763218554787642797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530302737165625534094917 99431763218554787642797)
                  ·
                    refine ⟨37286911206958045366049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99431763218554787642797 37286911206958045366049)
                    ·
                      rfl

theorem cell22_108924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_108924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108924 prefixEnd_108924 := by exact prefixLift 108924
  have htrace : WordTrace (prefixWord ++ tailWord_108924) baseStart_108924 baseEnd_108924 := by
    simpa [prefixWord, tailWord_108924, baseEnd_108924] using wordTrace_append hprefix tailTrace_108924
  have hstable : (prefixWord ++ tailWord_108924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108924).length < 2 ^ (prefixWord ++ tailWord_108924).sum := by decide
  have hdescent : baseEnd_108924 < baseStart_108924 := by decide
  rcases family_descends (prefixWord ++ tailWord_108924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108937 : List Nat := [1, 2, 1, 1, 6, 11]
def baseStart_108937 : Nat := 118140960795 + 108937 * 2 ^ 59
def prefixEnd_108937 : Nat := 4983230072969 + 3 ^ 40 * 108937 * 2
def baseEnd_108937 : Nat := 460387177439880799889

theorem tailTrace_108937 : CollatzResearch.WordTrace tailWord_108937 prefixEnd_108937 460387177439880799889 := by
  unfold tailWord_108937
  simp only [CollatzResearch.WordTrace]
  refine ⟨3973258806347328803493065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2648839204231552535662043 3973258806347328803493065)
  ·
    refine ⟨2979944104760496602619799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3973258806347328803493065 2979944104760496602619799)
    ·
      refine ⟨4469916157140744903929699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2979944104760496602619799 4469916157140744903929699)
      ·
        refine ⟨6704874235711117355894549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4469916157140744903929699 6704874235711117355894549)
        ·
          refine ⟨314290979798958626057557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6704874235711117355894549 314290979798958626057557)
          ·
            refine ⟨460387177439880799889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 314290979798958626057557 460387177439880799889)
            ·
              rfl

theorem cell22_108937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 11].length) (baseStart_108937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108937 prefixEnd_108937 := by exact prefixLift 108937
  have htrace : WordTrace (prefixWord ++ tailWord_108937) baseStart_108937 baseEnd_108937 := by
    simpa [prefixWord, tailWord_108937, baseEnd_108937] using wordTrace_append hprefix tailTrace_108937
  have hstable : (prefixWord ++ tailWord_108937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108937).length < 2 ^ (prefixWord ++ tailWord_108937).sum := by decide
  have hdescent : baseEnd_108937 < baseStart_108937 := by decide
  rcases family_descends (prefixWord ++ tailWord_108937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108939 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 2, 4]
def baseStart_108939 : Nat := 118140960795 + 108939 * 2 ^ 59
def prefixEnd_108939 : Nat := 4983230072969 + 3 ^ 40 * 108939 * 2
def baseEnd_108939 : Nat := 37292046013503006241003

theorem tailTrace_108939 : CollatzResearch.WordTrace tailWord_108939 prefixEnd_108939 37292046013503006241003 := by
  unfold tailWord_108939
  simp only [CollatzResearch.WordTrace]
  refine ⟨3973331752340083145065871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2648887834893388763377247 3973331752340083145065871)
  ·
    refine ⟨5959997628510124717598807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3973331752340083145065871 5959997628510124717598807)
    ·
      refine ⟨8939996442765187076398211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5959997628510124717598807 8939996442765187076398211)
      ·
        refine ⟨13409994664147780614597317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8939996442765187076398211 13409994664147780614597317)
        ·
          refine ⟨2514373999527708865236997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13409994664147780614597317 2514373999527708865236997)
          ·
            refine ⟨471445124911445412231937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2514373999527708865236997 471445124911445412231937)
            ·
              refine ⟨353583843683584059173953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471445124911445412231937 353583843683584059173953)
              ·
                refine ⟨265187882762688044380465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353583843683584059173953 265187882762688044380465)
                ·
                  refine ⟨198890912072016033285349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265187882762688044380465 198890912072016033285349)
                  ·
                    refine ⟨37292046013503006241003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 198890912072016033285349 37292046013503006241003)
                    ·
                      rfl

theorem cell22_108939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 4].length) (baseStart_108939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108939 prefixEnd_108939 := by exact prefixLift 108939
  have htrace : WordTrace (prefixWord ++ tailWord_108939) baseStart_108939 baseEnd_108939 := by
    simpa [prefixWord, tailWord_108939, baseEnd_108939] using wordTrace_append hprefix tailTrace_108939
  have hstable : (prefixWord ++ tailWord_108939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108939).length < 2 ^ (prefixWord ++ tailWord_108939).sum := by decide
  have hdescent : baseEnd_108939 < baseStart_108939 := by decide
  rcases family_descends (prefixWord ++ tailWord_108939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108954 : List Nat := [3, 1, 1, 4, 1, 2, 3, 7]
def baseStart_108954 : Nat := 118140960795 + 108954 * 2 ^ 59
def prefixEnd_108954 : Nat := 4983230072969 + 3 ^ 40 * 108954 * 2
def baseEnd_108954 : Nat := 4144131202227551901773

theorem tailTrace_108954 : CollatzResearch.WordTrace tailWord_108954 prefixEnd_108954 4144131202227551901773 := by
  unfold tailWord_108954
  simp only [CollatzResearch.WordTrace]
  refine ⟨993469711821435176715479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2649252564857160471241277 993469711821435176715479)
  ·
    refine ⟨1490204567732152765073219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 993469711821435176715479 1490204567732152765073219)
    ·
      refine ⟨2235306851598229147609829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1490204567732152765073219 2235306851598229147609829)
      ·
        refine ⟨419120034674667965176843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2235306851598229147609829 419120034674667965176843)
        ·
          refine ⟨628680052012001947765265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419120034674667965176843 628680052012001947765265)
          ·
            refine ⟨471510039009001460823949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628680052012001947765265 471510039009001460823949)
            ·
              refine ⟨176816264628375547808981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 471510039009001460823949 176816264628375547808981)
              ·
                refine ⟨4144131202227551901773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 176816264628375547808981 4144131202227551901773)
                ·
                  rfl

theorem cell22_108954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_108954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108954 prefixEnd_108954 := by exact prefixLift 108954
  have htrace : WordTrace (prefixWord ++ tailWord_108954) baseStart_108954 baseEnd_108954 := by
    simpa [prefixWord, tailWord_108954, baseEnd_108954] using wordTrace_append hprefix tailTrace_108954
  have hstable : (prefixWord ++ tailWord_108954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108954).length < 2 ^ (prefixWord ++ tailWord_108954).sum := by decide
  have hdescent : baseEnd_108954 < baseStart_108954 := by decide
  rcases family_descends (prefixWord ++ tailWord_108954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108958 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_108958 : Nat := 118140960795 + 108958 * 2 ^ 59
def prefixEnd_108958 : Nat := 4983230072969 + 3 ^ 40 * 108958 * 2
def baseEnd_108958 : Nat := 37298550101793290015945

theorem tailTrace_108958 : CollatzResearch.WordTrace tailWord_108958 prefixEnd_108958 37298550101793290015945 := by
  unfold tailWord_108958
  simp only [CollatzResearch.WordTrace]
  refine ⟨496753092408906173750941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2649349826180832926671685 496753092408906173750941)
  ·
    refine ⟨186282409653339815156603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 496753092408906173750941 186282409653339815156603)
    ·
      refine ⟨279423614480009722734905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186282409653339815156603 279423614480009722734905)
      ·
        refine ⟨209567710860007292051179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279423614480009722734905 209567710860007292051179)
        ·
          refine ⟨314351566290010938076769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209567710860007292051179 314351566290010938076769)
          ·
            refine ⟨235763674717508203557577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314351566290010938076769 235763674717508203557577)
            ·
              refine ⟨176822756038131152668183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235763674717508203557577 176822756038131152668183)
              ·
                refine ⟨265234134057196729002275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176822756038131152668183 265234134057196729002275)
                ·
                  refine ⟨397851201085795093503413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265234134057196729002275 397851201085795093503413)
                  ·
                    refine ⟨37298550101793290015945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 397851201085795093503413 37298550101793290015945)
                    ·
                      rfl

theorem cell22_108958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_108958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108958 prefixEnd_108958 := by exact prefixLift 108958
  have htrace : WordTrace (prefixWord ++ tailWord_108958) baseStart_108958 baseEnd_108958 := by
    simpa [prefixWord, tailWord_108958, baseEnd_108958] using wordTrace_append hprefix tailTrace_108958
  have hstable : (prefixWord ++ tailWord_108958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108958).length < 2 ^ (prefixWord ++ tailWord_108958).sum := by decide
  have hdescent : baseEnd_108958 < baseStart_108958 := by decide
  rcases family_descends (prefixWord ++ tailWord_108958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108999 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 7]
def baseStart_108999 : Nat := 118140960795 + 108999 * 2 ^ 59
def prefixEnd_108999 : Nat := 4983230072969 + 3 ^ 40 * 108999 * 2
def baseEnd_108999 : Nat := 12437528413227616580273

theorem tailTrace_108999 : CollatzResearch.WordTrace tailWord_108999 prefixEnd_108999 12437528413227616580273 := by
  unfold tailWord_108999
  simp only [CollatzResearch.WordTrace]
  refine ⟨3975520132122713392250051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2650346754748475594833367 3975520132122713392250051)
  ·
    refine ⟨5963280198184070088375077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3975520132122713392250051 5963280198184070088375077)
    ·
      refine ⟨1118115037159513141570327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5963280198184070088375077 1118115037159513141570327)
      ·
        refine ⟨1677172555739269712355491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118115037159513141570327 1677172555739269712355491)
        ·
          refine ⟨2515758833608904568533237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677172555739269712355491 2515758833608904568533237)
          ·
            refine ⟨235852390650834803299991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2515758833608904568533237 235852390650834803299991)
            ·
              refine ⟨353778585976252204949987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235852390650834803299991 353778585976252204949987)
              ·
                refine ⟨530667878964378307424981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353778585976252204949987 530667878964378307424981)
                ·
                  refine ⟨12437528413227616580273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 530667878964378307424981 12437528413227616580273)
                  ·
                    rfl

theorem cell22_108999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 7].length) (baseStart_108999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_108999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_108999 prefixEnd_108999 := by exact prefixLift 108999
  have htrace : WordTrace (prefixWord ++ tailWord_108999) baseStart_108999 baseEnd_108999 := by
    simpa [prefixWord, tailWord_108999, baseEnd_108999] using wordTrace_append hprefix tailTrace_108999
  have hstable : (prefixWord ++ tailWord_108999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108999).length < 2 ^ (prefixWord ++ tailWord_108999).sum := by decide
  have hdescent : baseEnd_108999 < baseStart_108999 := by decide
  rcases family_descends (prefixWord ++ tailWord_108999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109037 : List Nat := [1, 5, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_109037 : Nat := 118140960795 + 109037 * 2 ^ 59
def prefixEnd_109037 : Nat := 4983230072969 + 3 ^ 40 * 109037 * 2
def baseEnd_109037 : Nat := 37325593416263417290703

theorem tailTrace_109037 : CollatzResearch.WordTrace tailWord_109037 prefixEnd_109037 37325593416263417290703 := by
  unfold tailWord_109037
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976906105985045882133365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2651270737323363921422243 3976906105985045882133365)
  ·
    refine ⟨372834947436098051450003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3976906105985045882133365 372834947436098051450003)
    ·
      refine ⟨559252421154147077175005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372834947436098051450003 559252421154147077175005)
      ·
        refine ⟨209719657932805153940627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 559252421154147077175005 209719657932805153940627)
        ·
          refine ⟨314579486899207730910941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209719657932805153940627 314579486899207730910941)
          ·
            refine ⟨117967307587202899091603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314579486899207730910941 117967307587202899091603)
            ·
              refine ⟨176950961380804348637405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117967307587202899091603 176950961380804348637405)
              ·
                refine ⟨66356610517801630739027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176950961380804348637405 66356610517801630739027)
                ·
                  refine ⟨99534915776702446108541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66356610517801630739027 99534915776702446108541)
                  ·
                    refine ⟨37325593416263417290703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99534915776702446108541 37325593416263417290703)
                    ·
                      rfl

theorem cell22_109037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_109037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109037 prefixEnd_109037 := by exact prefixLift 109037
  have htrace : WordTrace (prefixWord ++ tailWord_109037) baseStart_109037 baseEnd_109037 := by
    simpa [prefixWord, tailWord_109037, baseEnd_109037] using wordTrace_append hprefix tailTrace_109037
  have hstable : (prefixWord ++ tailWord_109037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109037).length < 2 ^ (prefixWord ++ tailWord_109037).sum := by decide
  have hdescent : baseEnd_109037 < baseStart_109037 := by decide
  rcases family_descends (prefixWord ++ tailWord_109037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109061 : List Nat := [1, 3, 1, 1, 2, 2, 2, 6, 4]
def baseStart_109061 : Nat := 118140960795 + 109061 * 2 ^ 59
def prefixEnd_109061 : Nat := 4983230072969 + 3 ^ 40 * 109061 * 2
def baseEnd_109061 : Nat := 12444603035578451563543

theorem tailTrace_109061 : CollatzResearch.WordTrace tailWord_109061 prefixEnd_109061 12444603035578451563543 := by
  unfold tailWord_109061
  simp only [CollatzResearch.WordTrace]
  refine ⟨3977781457898097981007037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2651854305265398654004691 3977781457898097981007037)
  ·
    refine ⟨1491668046711786742877639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3977781457898097981007037 1491668046711786742877639)
    ·
      refine ⟨2237502070067680114316459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491668046711786742877639 2237502070067680114316459)
      ·
        refine ⟨3356253105101520171474689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2237502070067680114316459 3356253105101520171474689)
        ·
          refine ⟨2517189828826140128606017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3356253105101520171474689 2517189828826140128606017)
          ·
            refine ⟨1887892371619605096454513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2517189828826140128606017 1887892371619605096454513)
            ·
              refine ⟨1415919278714703822340885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887892371619605096454513 1415919278714703822340885)
              ·
                refine ⟨66371216189751741672229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1415919278714703822340885 66371216189751741672229)
                ·
                  refine ⟨12444603035578451563543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66371216189751741672229 12444603035578451563543)
                  ·
                    rfl

theorem cell22_109061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_109061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109061 prefixEnd_109061 := by exact prefixLift 109061
  have htrace : WordTrace (prefixWord ++ tailWord_109061) baseStart_109061 baseEnd_109061 := by
    simpa [prefixWord, tailWord_109061, baseEnd_109061] using wordTrace_append hprefix tailTrace_109061
  have hstable : (prefixWord ++ tailWord_109061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109061).length < 2 ^ (prefixWord ++ tailWord_109061).sum := by decide
  have hdescent : baseEnd_109061 < baseStart_109061 := by decide
  rcases family_descends (prefixWord ++ tailWord_109061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109089 : List Nat := [1, 2, 3, 2, 2, 1, 1, 10]
def baseStart_109089 : Nat := 118140960795 + 109089 * 2 ^ 59
def prefixEnd_109089 : Nat := 4983230072969 + 3 ^ 40 * 109089 * 2
def baseEnd_109089 : Nat := 4149266008772512776727

theorem tailTrace_109089 : CollatzResearch.WordTrace tailWord_109089 prefixEnd_109089 4149266008772512776727 := by
  unfold tailWord_109089
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978802701796658763026321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2652535134531105842017547 3978802701796658763026321)
  ·
    refine ⟨2984102026347494072269741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3978802701796658763026321 2984102026347494072269741)
    ·
      refine ⟨1119038259880310277101153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2984102026347494072269741 1119038259880310277101153)
      ·
        refine ⟨839278694910232707825865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1119038259880310277101153 839278694910232707825865)
        ·
          refine ⟨629459021182674530869399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 839278694910232707825865 629459021182674530869399)
          ·
            refine ⟨944188531774011796304099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629459021182674530869399 944188531774011796304099)
            ·
              refine ⟨1416282797661017694456149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944188531774011796304099 1416282797661017694456149)
              ·
                refine ⟨4149266008772512776727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1416282797661017694456149 4149266008772512776727)
                ·
                  rfl

theorem cell22_109089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 10].length) (baseStart_109089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109089 prefixEnd_109089 := by exact prefixLift 109089
  have htrace : WordTrace (prefixWord ++ tailWord_109089) baseStart_109089 baseEnd_109089 := by
    simpa [prefixWord, tailWord_109089, baseEnd_109089] using wordTrace_append hprefix tailTrace_109089
  have hstable : (prefixWord ++ tailWord_109089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109089).length < 2 ^ (prefixWord ++ tailWord_109089).sum := by decide
  have hdescent : baseEnd_109089 < baseStart_109089 := by decide
  rcases family_descends (prefixWord ++ tailWord_109089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109091 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 2, 4]
def baseStart_109091 : Nat := 118140960795 + 109091 * 2 ^ 59
def prefixEnd_109091 : Nat := 4983230072969 + 3 ^ 40 * 109091 * 2
def baseEnd_109091 : Nat := 37344078719825276440537

theorem tailTrace_109091 : CollatzResearch.WordTrace tailWord_109091 prefixEnd_109091 37344078719825276440537 := by
  unfold tailWord_109091
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978875647789413104599127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2652583765192942069732751 3978875647789413104599127)
  ·
    refine ⟨5968313471684119656898691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3978875647789413104599127 5968313471684119656898691)
    ·
      refine ⟨8952470207526179485348037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5968313471684119656898691 8952470207526179485348037)
      ·
        refine ⟨1678588163911158653502757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8952470207526179485348037 1678588163911158653502757)
        ·
          refine ⟨314735280733342247531767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1678588163911158653502757 314735280733342247531767)
          ·
            refine ⟨472102921100013371297651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314735280733342247531767 472102921100013371297651)
            ·
              refine ⟨708154381650020056946477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472102921100013371297651 708154381650020056946477)
              ·
                refine ⟨265557893118757521354929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 708154381650020056946477 265557893118757521354929)
                ·
                  refine ⟨199168419839068141016197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265557893118757521354929 199168419839068141016197)
                  ·
                    refine ⟨37344078719825276440537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199168419839068141016197 37344078719825276440537)
                    ·
                      rfl

theorem cell22_109091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 4].length) (baseStart_109091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109091 prefixEnd_109091 := by exact prefixLift 109091
  have htrace : WordTrace (prefixWord ++ tailWord_109091) baseStart_109091 baseEnd_109091 := by
    simpa [prefixWord, tailWord_109091, baseEnd_109091] using wordTrace_append hprefix tailTrace_109091
  have hstable : (prefixWord ++ tailWord_109091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109091).length < 2 ^ (prefixWord ++ tailWord_109091).sum := by decide
  have hdescent : baseEnd_109091 < baseStart_109091 := by decide
  rcases family_descends (prefixWord ++ tailWord_109091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109110 : List Nat := [5, 1, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_109110 : Nat := 118140960795 + 109110 * 2 ^ 59
def prefixEnd_109110 : Nat := 4983230072969 + 3 ^ 40 * 109110 * 2
def baseEnd_109110 : Nat := 37350582808115560215479

theorem tailTrace_109110 : CollatzResearch.WordTrace tailWord_109110 prefixEnd_109110 37350582808115560215479 := by
  unfold tailWord_109110
  simp only [CollatzResearch.WordTrace]
  refine ⟨248723039670036209346299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2653045756480386233027189 248723039670036209346299)
  ·
    refine ⟨373084559505054314019449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248723039670036209346299 373084559505054314019449)
    ·
      refine ⟨279813419628790735514587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373084559505054314019449 279813419628790735514587)
      ·
        refine ⟨419720129443186103271881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279813419628790735514587 419720129443186103271881)
        ·
          refine ⟨314790097082389577453911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419720129443186103271881 314790097082389577453911)
          ·
            refine ⟨472185145623584366180867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314790097082389577453911 472185145623584366180867)
            ·
              refine ⟨708277718435376549271301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472185145623584366180867 708277718435376549271301)
              ·
                refine ⟨132802072206633102988369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 708277718435376549271301 132802072206633102988369)
                ·
                  refine ⟨99601554154974827241277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132802072206633102988369 99601554154974827241277)
                  ·
                    refine ⟨37350582808115560215479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99601554154974827241277 37350582808115560215479)
                    ·
                      rfl

theorem cell22_109110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_109110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109110 prefixEnd_109110 := by exact prefixLift 109110
  have htrace : WordTrace (prefixWord ++ tailWord_109110) baseStart_109110 baseEnd_109110 := by
    simpa [prefixWord, tailWord_109110, baseEnd_109110] using wordTrace_append hprefix tailTrace_109110
  have hstable : (prefixWord ++ tailWord_109110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109110).length < 2 ^ (prefixWord ++ tailWord_109110).sum := by decide
  have hdescent : baseEnd_109110 < baseStart_109110 := by decide
  rcases family_descends (prefixWord ++ tailWord_109110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109119 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 1, 8]
def baseStart_109119 : Nat := 118140960795 + 109119 * 2 ^ 59
def prefixEnd_109119 : Nat := 4983230072969 + 3 ^ 40 * 109119 * 2
def baseEnd_109119 : Nat := 37353663692042536740451

theorem tailTrace_109119 : CollatzResearch.WordTrace tailWord_109119 prefixEnd_109119 37353663692042536740451 := by
  unfold tailWord_109119
  simp only [CollatzResearch.WordTrace]
  refine ⟨3979896891687973886618411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2653264594458649257745607 3979896891687973886618411)
  ·
    refine ⟨5969845337531960829927617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3979896891687973886618411 5969845337531960829927617)
    ·
      refine ⟨4477384003148970622445713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5969845337531960829927617 4477384003148970622445713)
      ·
        refine ⟨3358038002361727966834285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4477384003148970622445713 3358038002361727966834285)
        ·
          refine ⟨1259264250885647987562857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3358038002361727966834285 1259264250885647987562857)
          ·
            refine ⟨944448188164235990672143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1259264250885647987562857 944448188164235990672143)
            ·
              refine ⟨1416672282246353986008215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944448188164235990672143 1416672282246353986008215)
              ·
                refine ⟨2125008423369530979012323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1416672282246353986008215 2125008423369530979012323)
                ·
                  refine ⟨3187512635054296468518485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2125008423369530979012323 3187512635054296468518485)
                  ·
                    refine ⟨37353663692042536740451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3187512635054296468518485 37353663692042536740451)
                    ·
                      rfl

theorem cell22_109119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_109119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109119 prefixEnd_109119 := by exact prefixLift 109119
  have htrace : WordTrace (prefixWord ++ tailWord_109119) baseStart_109119 baseEnd_109119 := by
    simpa [prefixWord, tailWord_109119, baseEnd_109119] using wordTrace_append hprefix tailTrace_109119
  have hstable : (prefixWord ++ tailWord_109119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109119).length < 2 ^ (prefixWord ++ tailWord_109119).sum := by decide
  have hdescent : baseEnd_109119 < baseStart_109119 := by decide
  rcases family_descends (prefixWord ++ tailWord_109119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109138 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_109138 : Nat := 118140960795 + 109138 * 2 ^ 59
def prefixEnd_109138 : Nat := 4983230072969 + 3 ^ 40 * 109138 * 2
def baseEnd_109138 : Nat := 37360167780332820515393

theorem tailTrace_109138 : CollatzResearch.WordTrace tailWord_109138 prefixEnd_109138 37360167780332820515393 := by
  unfold tailWord_109138
  simp only [CollatzResearch.WordTrace]
  refine ⟨995147469654785032890017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2653726585746093421040045 995147469654785032890017)
  ·
    refine ⟨746360602241088774667513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 995147469654785032890017 746360602241088774667513)
    ·
      refine ⟨559770451680816581000635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 746360602241088774667513 559770451680816581000635)
      ·
        refine ⟨839655677521224871500953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559770451680816581000635 839655677521224871500953)
        ·
          refine ⟨629741758140918653625715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 839655677521224871500953 629741758140918653625715)
          ·
            refine ⟨944612637211377980438573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629741758140918653625715 944612637211377980438573)
            ·
              refine ⟨354229738954266742664465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 944612637211377980438573 354229738954266742664465)
              ·
                refine ⟨265672304215700056998349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354229738954266742664465 265672304215700056998349)
                ·
                  refine ⟨99627114080887521374381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 265672304215700056998349 99627114080887521374381)
                  ·
                    refine ⟨37360167780332820515393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99627114080887521374381 37360167780332820515393)
                    ·
                      rfl

theorem cell22_109138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_109138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109138 prefixEnd_109138 := by exact prefixLift 109138
  have htrace : WordTrace (prefixWord ++ tailWord_109138) baseStart_109138 baseEnd_109138 := by
    simpa [prefixWord, tailWord_109138, baseEnd_109138] using wordTrace_append hprefix tailTrace_109138
  have hstable : (prefixWord ++ tailWord_109138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109138).length < 2 ^ (prefixWord ++ tailWord_109138).sum := by decide
  have hdescent : baseEnd_109138 < baseStart_109138 := by decide
  rcases family_descends (prefixWord ++ tailWord_109138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109155 : List Nat := [1, 1, 1, 5, 1, 2, 4, 3, 1, 3]
def baseStart_109155 : Nat := 118140960795 + 109155 * 2 ^ 59
def prefixEnd_109155 : Nat := 4983230072969 + 3 ^ 40 * 109155 * 2
def baseEnd_109155 : Nat := 37365987227750442840341

theorem tailTrace_109155 : CollatzResearch.WordTrace tailWord_109155 prefixEnd_109155 37365987227750442840341 := by
  unfold tailWord_109155
  simp only [CollatzResearch.WordTrace]
  refine ⟨3981209919557552034928919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2654139946371701356619279 3981209919557552034928919)
  ·
    refine ⟨5971814879336328052393379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3981209919557552034928919 5971814879336328052393379)
    ·
      refine ⟨8957722319004492078590069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5971814879336328052393379 8957722319004492078590069)
      ·
        refine ⟨839786467406671132367819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8957722319004492078590069 839786467406671132367819)
        ·
          refine ⟨1259679701110006698551729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839786467406671132367819 1259679701110006698551729)
          ·
            refine ⟨944759775832505023913797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1259679701110006698551729 944759775832505023913797)
            ·
              refine ⟨177142457968594691983837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 944759775832505023913797 177142457968594691983837)
              ·
                refine ⟨66428421738223009493939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177142457968594691983837 66428421738223009493939)
                ·
                  refine ⟨99642632607334514240909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66428421738223009493939 99642632607334514240909)
                  ·
                    refine ⟨37365987227750442840341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99642632607334514240909 37365987227750442840341)
                    ·
                      rfl

theorem cell22_109155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 1, 3].length) (baseStart_109155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109155 prefixEnd_109155 := by exact prefixLift 109155
  have htrace : WordTrace (prefixWord ++ tailWord_109155) baseStart_109155 baseEnd_109155 := by
    simpa [prefixWord, tailWord_109155, baseEnd_109155] using wordTrace_append hprefix tailTrace_109155
  have hstable : (prefixWord ++ tailWord_109155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109155).length < 2 ^ (prefixWord ++ tailWord_109155).sum := by decide
  have hdescent : baseEnd_109155 < baseStart_109155 := by decide
  rcases family_descends (prefixWord ++ tailWord_109155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109230 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_109230 : Nat := 118140960795 + 109230 * 2 ^ 59
def prefixEnd_109230 : Nat := 4983230072969 + 3 ^ 40 * 109230 * 2
def baseEnd_109230 : Nat := 12463887086825082405037

theorem tailTrace_109230 : CollatzResearch.WordTrace tailWord_109230 prefixEnd_109230 12463887086825082405037 := by
  unfold tailWord_109230
  simp only [CollatzResearch.WordTrace]
  refine ⟨497993174285729980488643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2655963596190559895939429 497993174285729980488643)
  ·
    refine ⟨746989761428594970732965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 497993174285729980488643 746989761428594970732965)
    ·
      refine ⟨140060580267861557012431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 746989761428594970732965 140060580267861557012431)
      ·
        refine ⟨210090870401792335518647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140060580267861557012431 210090870401792335518647)
        ·
          refine ⟨315136305602688503277971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210090870401792335518647 315136305602688503277971)
          ·
            refine ⟨472704458404032754916957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315136305602688503277971 472704458404032754916957)
            ·
              refine ⟨177264171901512283093859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 472704458404032754916957 177264171901512283093859)
              ·
                refine ⟨265896257852268424640789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177264171901512283093859 265896257852268424640789)
                ·
                  refine ⟨12463887086825082405037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 265896257852268424640789 12463887086825082405037)
                  ·
                    rfl

theorem cell22_109230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_109230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109230 prefixEnd_109230 := by exact prefixLift 109230
  have htrace : WordTrace (prefixWord ++ tailWord_109230) baseStart_109230 baseEnd_109230 := by
    simpa [prefixWord, tailWord_109230, baseEnd_109230] using wordTrace_append hprefix tailTrace_109230
  have hstable : (prefixWord ++ tailWord_109230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109230).length < 2 ^ (prefixWord ++ tailWord_109230).sum := by decide
  have hdescent : baseEnd_109230 < baseStart_109230 := by decide
  rcases family_descends (prefixWord ++ tailWord_109230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109245 : List Nat := [1, 4, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_109245 : Nat := 118140960795 + 109245 * 2 ^ 59
def prefixEnd_109245 : Nat := 4983230072969 + 3 ^ 40 * 109245 * 2
def baseEnd_109245 : Nat := 37396796067020208090065

theorem tailTrace_109245 : CollatzResearch.WordTrace tailWord_109245 prefixEnd_109245 37396796067020208090065 := by
  unfold tailWord_109245
  simp only [CollatzResearch.WordTrace]
  refine ⟨3984492489231497405705189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2656328326154331603803459 3984492489231497405705189)
  ·
    refine ⟨747092341730905763569723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3984492489231497405705189 747092341730905763569723)
    ·
      refine ⟨1120638512596358645354585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747092341730905763569723 1120638512596358645354585)
      ·
        refine ⟨840478884447268984015939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1120638512596358645354585 840478884447268984015939)
        ·
          refine ⟨1260718326670903476023909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840478884447268984015939 1260718326670903476023909)
          ·
            refine ⟨236384686250794401754483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1260718326670903476023909 236384686250794401754483)
            ·
              refine ⟨354577029376191602631725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236384686250794401754483 354577029376191602631725)
              ·
                refine ⟨132966386016071850986897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354577029376191602631725 132966386016071850986897)
                ·
                  refine ⟨99724789512053888240173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132966386016071850986897 99724789512053888240173)
                  ·
                    refine ⟨37396796067020208090065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99724789512053888240173 37396796067020208090065)
                    ·
                      rfl

theorem cell22_109245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_109245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109245 prefixEnd_109245 := by exact prefixLift 109245
  have htrace : WordTrace (prefixWord ++ tailWord_109245) baseStart_109245 baseEnd_109245 := by
    simpa [prefixWord, tailWord_109245, baseEnd_109245] using wordTrace_append hprefix tailTrace_109245
  have hstable : (prefixWord ++ tailWord_109245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109245).length < 2 ^ (prefixWord ++ tailWord_109245).sum := by decide
  have hdescent : baseEnd_109245 < baseStart_109245 := by decide
  rcases family_descends (prefixWord ++ tailWord_109245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109249 : List Nat := [1, 2, 6, 2, 1, 2, 1, 2, 1, 4]
def baseStart_109249 : Nat := 118140960795 + 109249 * 2 ^ 59
def prefixEnd_109249 : Nat := 4983230072969 + 3 ^ 40 * 109249 * 2
def baseEnd_109249 : Nat := 37398165348765530990053

theorem tailTrace_109249 : CollatzResearch.WordTrace tailWord_109249 prefixEnd_109249 37398165348765530990053 := by
  unfold tailWord_109249
  simp only [CollatzResearch.WordTrace]
  refine ⟨3984638381217006088850801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2656425587478004059233867 3984638381217006088850801)
  ·
    refine ⟨2988478785912754566638101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3984638381217006088850801 2988478785912754566638101)
    ·
      refine ⟨140084943089660370311161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2988478785912754566638101 140084943089660370311161)
      ·
        refine ⟨105063707317245277733371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140084943089660370311161 105063707317245277733371)
        ·
          refine ⟨157595560975867916600057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105063707317245277733371 157595560975867916600057)
          ·
            refine ⟨118196670731900937450043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157595560975867916600057 118196670731900937450043)
            ·
              refine ⟨177295006097851406175065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118196670731900937450043 177295006097851406175065)
              ·
                refine ⟨132971254573388554631299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177295006097851406175065 132971254573388554631299)
                ·
                  refine ⟨199456881860082831946949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132971254573388554631299 199456881860082831946949)
                  ·
                    refine ⟨37398165348765530990053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199456881860082831946949 37398165348765530990053)
                    ·
                      rfl

theorem cell22_109249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_109249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109249 prefixEnd_109249 := by exact prefixLift 109249
  have htrace : WordTrace (prefixWord ++ tailWord_109249) baseStart_109249 baseEnd_109249 := by
    simpa [prefixWord, tailWord_109249, baseEnd_109249] using wordTrace_append hprefix tailTrace_109249
  have hstable : (prefixWord ++ tailWord_109249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109249).length < 2 ^ (prefixWord ++ tailWord_109249).sum := by decide
  have hdescent : baseEnd_109249 < baseStart_109249 := by decide
  rcases family_descends (prefixWord ++ tailWord_109249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109260 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 2, 4]
def baseStart_109260 : Nat := 118140960795 + 109260 * 2 ^ 59
def prefixEnd_109260 : Nat := 4983230072969 + 3 ^ 40 * 109260 * 2
def baseEnd_109260 : Nat := 37401930873565168965019

theorem tailTrace_109260 : CollatzResearch.WordTrace tailWord_109260 prefixEnd_109260 37401930873565168965019 := by
  unfold tailWord_109260
  simp only [CollatzResearch.WordTrace]
  refine ⟨1992519792088577483750617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2656693056118103311667489 1992519792088577483750617)
  ·
    refine ⟨1494389844066433112812963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1992519792088577483750617 1494389844066433112812963)
    ·
      refine ⟨2241584766099649669219445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1494389844066433112812963 2241584766099649669219445)
      ·
        refine ⟨210148571821842156489323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2241584766099649669219445 210148571821842156489323)
        ·
          refine ⟨315222857732763234733985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210148571821842156489323 315222857732763234733985)
          ·
            refine ⟨236417143299572426050489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315222857732763234733985 236417143299572426050489)
            ·
              refine ⟨177312857474679319537867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236417143299572426050489 177312857474679319537867)
              ·
                refine ⟨265969286212018979306801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177312857474679319537867 265969286212018979306801)
                ·
                  refine ⟨199476964659014234480101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265969286212018979306801 199476964659014234480101)
                  ·
                    refine ⟨37401930873565168965019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199476964659014234480101 37401930873565168965019)
                    ·
                      rfl

theorem cell22_109260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_109260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109260 prefixEnd_109260 := by exact prefixLift 109260
  have htrace : WordTrace (prefixWord ++ tailWord_109260) baseStart_109260 baseEnd_109260 := by
    simpa [prefixWord, tailWord_109260, baseEnd_109260] using wordTrace_append hprefix tailTrace_109260
  have hstable : (prefixWord ++ tailWord_109260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109260).length < 2 ^ (prefixWord ++ tailWord_109260).sum := by decide
  have hdescent : baseEnd_109260 < baseStart_109260 := by decide
  rcases family_descends (prefixWord ++ tailWord_109260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109331 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 8]
def baseStart_109331 : Nat := 118140960795 + 109331 * 2 ^ 59
def prefixEnd_109331 : Nat := 4983230072969 + 3 ^ 40 * 109331 * 2
def baseEnd_109331 : Nat := 12475411874848216813267

theorem tailTrace_109331 : CollatzResearch.WordTrace tailWord_109331 prefixEnd_109331 12475411874848216813267 := by
  unfold tailWord_109331
  simp only [CollatzResearch.WordTrace]
  refine ⟨3987629166919934093335847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2658419444613289395557231 3987629166919934093335847)
  ·
    refine ⟨5981443750379901140003771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3987629166919934093335847 5981443750379901140003771)
    ·
      refine ⟨8972165625569851710005657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5981443750379901140003771 8972165625569851710005657)
      ·
        refine ⟨6729124219177388782504243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8972165625569851710005657 6729124219177388782504243)
        ·
          refine ⟨10093686328766083173756365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6729124219177388782504243 10093686328766083173756365)
          ·
            refine ⟨3785132373287281190158637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10093686328766083173756365 3785132373287281190158637)
            ·
              refine ⟨1419424639982730446309489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3785132373287281190158637 1419424639982730446309489)
              ·
                refine ⟨1064568479987047834732117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1419424639982730446309489 1064568479987047834732117)
                ·
                  refine ⟨12475411874848216813267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1064568479987047834732117 12475411874848216813267)
                  ·
                    rfl

theorem cell22_109331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 8].length) (baseStart_109331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109331 prefixEnd_109331 := by exact prefixLift 109331
  have htrace : WordTrace (prefixWord ++ tailWord_109331) baseStart_109331 baseEnd_109331 := by
    simpa [prefixWord, tailWord_109331, baseEnd_109331] using wordTrace_append hprefix tailTrace_109331
  have hstable : (prefixWord ++ tailWord_109331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109331).length < 2 ^ (prefixWord ++ tailWord_109331).sum := by decide
  have hdescent : baseEnd_109331 < baseStart_109331 := by decide
  rcases family_descends (prefixWord ++ tailWord_109331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109354 : List Nat := [3, 1, 4, 3, 1, 1, 3, 1, 5]
def baseStart_109354 : Nat := 118140960795 + 109354 * 2 ^ 59
def prefixEnd_109354 : Nat := 4983230072969 + 3 ^ 40 * 109354 * 2
def baseEnd_109354 : Nat := 12478036331526752371577

theorem tailTrace_109354 : CollatzResearch.WordTrace tailWord_109354 prefixEnd_109354 12478036331526752371577 := by
  unfold tailWord_109354
  simp only [CollatzResearch.WordTrace]
  refine ⟨997117011459152255355779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2658978697224406014282077 997117011459152255355779)
  ·
    refine ⟨1495675517188728383033669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 997117011459152255355779 1495675517188728383033669)
    ·
      refine ⟨280439159472886571818813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1495675517188728383033669 280439159472886571818813)
      ·
        refine ⟨105164684802332464432055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280439159472886571818813 105164684802332464432055)
        ·
          refine ⟨157747027203498696648083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105164684802332464432055 157747027203498696648083)
          ·
            refine ⟨236620540805248044972125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157747027203498696648083 236620540805248044972125)
            ·
              refine ⟨88732702801968016864547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236620540805248044972125 88732702801968016864547)
              ·
                refine ⟨133099054202952025296821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88732702801968016864547 133099054202952025296821)
                ·
                  refine ⟨12478036331526752371577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133099054202952025296821 12478036331526752371577)
                  ·
                    rfl

theorem cell22_109354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_109354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109354 prefixEnd_109354 := by exact prefixLift 109354
  have htrace : WordTrace (prefixWord ++ tailWord_109354) baseStart_109354 baseEnd_109354 := by
    simpa [prefixWord, tailWord_109354, baseEnd_109354] using wordTrace_append hprefix tailTrace_109354
  have hstable : (prefixWord ++ tailWord_109354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109354).length < 2 ^ (prefixWord ++ tailWord_109354).sum := by decide
  have hdescent : baseEnd_109354 < baseStart_109354 := by decide
  rcases family_descends (prefixWord ++ tailWord_109354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109483 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 6]
def baseStart_109483 : Nat := 118140960795 + 109483 * 2 ^ 59
def prefixEnd_109483 : Nat := 4983230072969 + 3 ^ 40 * 109483 * 2
def baseEnd_109483 : Nat := 12492756110288973546445

theorem tailTrace_109483 : CollatzResearch.WordTrace tailWord_109483 prefixEnd_109483 12492756110288973546445 := by
  unfold tailWord_109483
  simp only [CollatzResearch.WordTrace]
  refine ⟨3993173062369264052869103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2662115374912842701912735 3993173062369264052869103)
  ·
    refine ⟨5989759593553896079303655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3993173062369264052869103 5989759593553896079303655)
    ·
      refine ⟨8984639390330844118955483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5989759593553896079303655 8984639390330844118955483)
      ·
        refine ⟨13476959085496266178433225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8984639390330844118955483 13476959085496266178433225)
        ·
          refine ⟨10107719314122199633824919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13476959085496266178433225 10107719314122199633824919)
          ·
            refine ⟨15161578971183299450737379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10107719314122199633824919 15161578971183299450737379)
            ·
              refine ⟨22742368456774949176106069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15161578971183299450737379 22742368456774949176106069)
              ·
                refine ⟨266512130352831435657493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 22742368456774949176106069 266512130352831435657493)
                ·
                  refine ⟨12492756110288973546445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 266512130352831435657493 12492756110288973546445)
                  ·
                    rfl

theorem cell22_109483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 6].length) (baseStart_109483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109483 prefixEnd_109483 := by exact prefixLift 109483
  have htrace : WordTrace (prefixWord ++ tailWord_109483) baseStart_109483 baseEnd_109483 := by
    simpa [prefixWord, tailWord_109483, baseEnd_109483] using wordTrace_append hprefix tailTrace_109483
  have hstable : (prefixWord ++ tailWord_109483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109483).length < 2 ^ (prefixWord ++ tailWord_109483).sum := by decide
  have hdescent : baseEnd_109483 < baseStart_109483 := by decide
  rcases family_descends (prefixWord ++ tailWord_109483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109502 : List Nat := [4, 2, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_109502 : Nat := 118140960795 + 109502 * 2 ^ 59
def prefixEnd_109502 : Nat := 4983230072969 + 3 ^ 40 * 109502 * 2
def baseEnd_109502 : Nat := 37484772419157204414277

theorem tailTrace_109502 : CollatzResearch.WordTrace tailWord_109502 prefixEnd_109502 37484772419157204414277 := by
  unfold tailWord_109502
  simp only [CollatzResearch.WordTrace]
  refine ⟨499233256162553787226345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2662577366200286865207173 499233256162553787226345)
  ·
    refine ⟨374424942121915340419759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 499233256162553787226345 374424942121915340419759)
    ·
      refine ⟨561637413182873010629639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374424942121915340419759 561637413182873010629639)
      ·
        refine ⟨842456119774309515944459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561637413182873010629639 842456119774309515944459)
        ·
          refine ⟨1263684179661464273916689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842456119774309515944459 1263684179661464273916689)
          ·
            refine ⟨947763134746098205437517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1263684179661464273916689 947763134746098205437517)
            ·
              refine ⟨355411175529786827039069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 947763134746098205437517 355411175529786827039069)
              ·
                refine ⟨133279190823670060139651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355411175529786827039069 133279190823670060139651)
                ·
                  refine ⟨199918786235505090209477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133279190823670060139651 199918786235505090209477)
                  ·
                    refine ⟨37484772419157204414277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199918786235505090209477 37484772419157204414277)
                    ·
                      rfl

theorem cell22_109502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_109502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109502 prefixEnd_109502 := by exact prefixLift 109502
  have htrace : WordTrace (prefixWord ++ tailWord_109502) baseStart_109502 baseEnd_109502 := by
    simpa [prefixWord, tailWord_109502, baseEnd_109502] using wordTrace_append hprefix tailTrace_109502
  have hstable : (prefixWord ++ tailWord_109502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109502).length < 2 ^ (prefixWord ++ tailWord_109502).sum := by decide
  have hdescent : baseEnd_109502 < baseStart_109502 := by decide
  rcases family_descends (prefixWord ++ tailWord_109502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109510 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_109510 : Nat := 118140960795 + 109510 * 2 ^ 59
def prefixEnd_109510 : Nat := 4983230072969 + 3 ^ 40 * 109510 * 2
def baseEnd_109510 : Nat := 37487510982647850214253

theorem tailTrace_109510 : CollatzResearch.WordTrace tailWord_109510 prefixEnd_109510 37487510982647850214253 := by
  unfold tailWord_109510
  simp only [CollatzResearch.WordTrace]
  refine ⟨124817432289732739503187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2662771888847631776067989 124817432289732739503187)
  ·
    refine ⟨187226148434599109254781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124817432289732739503187 187226148434599109254781)
    ·
      refine ⟨70209805662974665970543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187226148434599109254781 70209805662974665970543)
      ·
        refine ⟨105314708494461998955815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70209805662974665970543 105314708494461998955815)
        ·
          refine ⟨157972062741692998433723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105314708494461998955815 157972062741692998433723)
          ·
            refine ⟨236958094112539497650585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157972062741692998433723 236958094112539497650585)
            ·
              refine ⟨177718570584404623237939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236958094112539497650585 177718570584404623237939)
              ·
                refine ⟨266577855876606934856909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177718570584404623237939 266577855876606934856909)
                ·
                  refine ⟨99966695953727600571341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266577855876606934856909 99966695953727600571341)
                  ·
                    refine ⟨37487510982647850214253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99966695953727600571341 37487510982647850214253)
                    ·
                      rfl

theorem cell22_109510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_109510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109510 prefixEnd_109510 := by exact prefixLift 109510
  have htrace : WordTrace (prefixWord ++ tailWord_109510) baseStart_109510 baseEnd_109510 := by
    simpa [prefixWord, tailWord_109510, baseEnd_109510] using wordTrace_append hprefix tailTrace_109510
  have hstable : (prefixWord ++ tailWord_109510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109510).length < 2 ^ (prefixWord ++ tailWord_109510).sum := by decide
  have hdescent : baseEnd_109510 < baseStart_109510 := by decide
  rcases family_descends (prefixWord ++ tailWord_109510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109513 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 5, 6]
def baseStart_109513 : Nat := 118140960795 + 109513 * 2 ^ 59
def prefixEnd_109513 : Nat := 4983230072969 + 3 ^ 40 * 109513 * 2
def baseEnd_109513 : Nat := 37488537943956842389243

theorem tailTrace_109513 : CollatzResearch.WordTrace tailWord_109513 prefixEnd_109513 37488537943956842389243 := by
  unfold tailWord_109513
  simp only [CollatzResearch.WordTrace]
  refine ⟨3994267252260579176461193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2662844834840386117640795 3994267252260579176461193)
  ·
    refine ⟨2995700439195434382345895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3994267252260579176461193 2995700439195434382345895)
    ·
      refine ⟨4493550658793151573518843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2995700439195434382345895 4493550658793151573518843)
      ·
        refine ⟨6740325988189727360278265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4493550658793151573518843 6740325988189727360278265)
        ·
          refine ⟨5055244491142295520208699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6740325988189727360278265 5055244491142295520208699)
          ·
            refine ⟨7582866736713443280313049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5055244491142295520208699 7582866736713443280313049)
            ·
              refine ⟨5687150052535082460234787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7582866736713443280313049 5687150052535082460234787)
              ·
                refine ⟨8530725078802623690352181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5687150052535082460234787 8530725078802623690352181)
                ·
                  refine ⟨799755476137745970970517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8530725078802623690352181 799755476137745970970517)
                  ·
                    refine ⟨37488537943956842389243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 799755476137745970970517 37488537943956842389243)
                    ·
                      rfl

theorem cell22_109513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_109513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109513 prefixEnd_109513 := by exact prefixLift 109513
  have htrace : WordTrace (prefixWord ++ tailWord_109513) baseStart_109513 baseEnd_109513 := by
    simpa [prefixWord, tailWord_109513, baseEnd_109513] using wordTrace_append hprefix tailTrace_109513
  have hstable : (prefixWord ++ tailWord_109513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109513).length < 2 ^ (prefixWord ++ tailWord_109513).sum := by decide
  have hdescent : baseEnd_109513 < baseStart_109513 := by decide
  rcases family_descends (prefixWord ++ tailWord_109513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109530 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_109530 : Nat := 118140960795 + 109530 * 2 ^ 59
def prefixEnd_109530 : Nat := 4983230072969 + 3 ^ 40 * 109530 * 2
def baseEnd_109530 : Nat := 37494357391374464714191

theorem tailTrace_109530 : CollatzResearch.WordTrace tailWord_109530 prefixEnd_109530 37494357391374464714191 := by
  unfold tailWord_109530
  simp only [CollatzResearch.WordTrace]
  refine ⟨998721823299747769957511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2663258195465994053220029 998721823299747769957511)
  ·
    refine ⟨1498082734949621654936267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 998721823299747769957511 1498082734949621654936267)
    ·
      refine ⟨2247124102424432482404401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1498082734949621654936267 2247124102424432482404401)
      ·
        refine ⟨1685343076818324361803301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2247124102424432482404401 1685343076818324361803301)
        ·
          refine ⟨316001826903435817838119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1685343076818324361803301 316001826903435817838119)
          ·
            refine ⟨474002740355153726757179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316001826903435817838119 474002740355153726757179)
            ·
              refine ⟨711004110532730590135769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474002740355153726757179 711004110532730590135769)
              ·
                refine ⟨533253082899547942601827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711004110532730590135769 533253082899547942601827)
                ·
                  refine ⟨799879624349321913902741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 533253082899547942601827 799879624349321913902741)
                  ·
                    refine ⟨37494357391374464714191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 799879624349321913902741 37494357391374464714191)
                    ·
                      rfl

theorem cell22_109530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_109530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109530 prefixEnd_109530 := by exact prefixLift 109530
  have htrace : WordTrace (prefixWord ++ tailWord_109530) baseStart_109530 baseEnd_109530 := by
    simpa [prefixWord, tailWord_109530, baseEnd_109530] using wordTrace_append hprefix tailTrace_109530
  have hstable : (prefixWord ++ tailWord_109530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109530).length < 2 ^ (prefixWord ++ tailWord_109530).sum := by decide
  have hdescent : baseEnd_109530 < baseStart_109530 := by decide
  rcases family_descends (prefixWord ++ tailWord_109530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109575 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 2, 6]
def baseStart_109575 : Nat := 118140960795 + 109575 * 2 ^ 59
def prefixEnd_109575 : Nat := 4983230072969 + 3 ^ 40 * 109575 * 2
def baseEnd_109575 : Nat := 37509761811009347339053

theorem tailTrace_109575 : CollatzResearch.WordTrace tailWord_109575 prefixEnd_109575 37509761811009347339053 := by
  unfold tailWord_109575
  simp only [CollatzResearch.WordTrace]
  refine ⟨3996528578035963765218179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2664352385357309176812119 3996528578035963765218179)
  ·
    refine ⟨5994792867053945647827269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3996528578035963765218179 5994792867053945647827269)
    ·
      refine ⟨1124023662572614808967613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5994792867053945647827269 1124023662572614808967613)
      ·
        refine ⟨421508873464730553362855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1124023662572614808967613 421508873464730553362855)
        ·
          refine ⟨632263310197095830044283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421508873464730553362855 632263310197095830044283)
          ·
            refine ⟨948394965295643745066425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632263310197095830044283 948394965295643745066425)
            ·
              refine ⟨711296223971732808799819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948394965295643745066425 711296223971732808799819)
              ·
                refine ⟨1066944335957599213199729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711296223971732808799819 1066944335957599213199729)
                ·
                  refine ⟨800208251968199409899797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1066944335957599213199729 800208251968199409899797)
                  ·
                    refine ⟨37509761811009347339053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 800208251968199409899797 37509761811009347339053)
                    ·
                      rfl

theorem cell22_109575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_109575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109575 prefixEnd_109575 := by exact prefixLift 109575
  have htrace : WordTrace (prefixWord ++ tailWord_109575) baseStart_109575 baseEnd_109575 := by
    simpa [prefixWord, tailWord_109575, baseEnd_109575] using wordTrace_append hprefix tailTrace_109575
  have hstable : (prefixWord ++ tailWord_109575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109575).length < 2 ^ (prefixWord ++ tailWord_109575).sum := by decide
  have hdescent : baseEnd_109575 < baseStart_109575 := by decide
  rcases family_descends (prefixWord ++ tailWord_109575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109628 : List Nat := [2, 2, 2, 2, 2, 4, 2, 2, 1, 3]
def baseStart_109628 : Nat := 118140960795 + 109628 * 2 ^ 59
def prefixEnd_109628 : Nat := 4983230072969 + 3 ^ 40 * 109628 * 2
def baseEnd_109628 : Nat := 37527904794134875763891

theorem tailTrace_109628 : CollatzResearch.WordTrace tailWord_109628 prefixEnd_109628 37527904794134875763891 := by
  unfold tailWord_109628
  simp only [CollatzResearch.WordTrace]
  refine ⟨1999230823421976908448769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2665641097895969211265025 1999230823421976908448769)
  ·
    refine ⟨1499423117566482681336577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1999230823421976908448769 1499423117566482681336577)
    ·
      refine ⟨1124567338174862011002433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1499423117566482681336577 1124567338174862011002433)
      ·
        refine ⟨843425503631146508251825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1124567338174862011002433 843425503631146508251825)
        ·
          refine ⟨632569127723359881188869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843425503631146508251825 632569127723359881188869)
          ·
            refine ⟨118606711448129977722913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 632569127723359881188869 118606711448129977722913)
            ·
              refine ⟨88955033586097483292185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118606711448129977722913 88955033586097483292185)
              ·
                refine ⟨66716275189573112469139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88955033586097483292185 66716275189573112469139)
                ·
                  refine ⟨100074412784359668703709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66716275189573112469139 100074412784359668703709)
                  ·
                    refine ⟨37527904794134875763891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100074412784359668703709 37527904794134875763891)
                    ·
                      rfl

theorem cell22_109628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_109628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109628 prefixEnd_109628 := by exact prefixLift 109628
  have htrace : WordTrace (prefixWord ++ tailWord_109628) baseStart_109628 baseEnd_109628 := by
    simpa [prefixWord, tailWord_109628, baseEnd_109628] using wordTrace_append hprefix tailTrace_109628
  have hstable : (prefixWord ++ tailWord_109628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109628).length < 2 ^ (prefixWord ++ tailWord_109628).sum := by decide
  have hdescent : baseEnd_109628 < baseStart_109628 := by decide
  rcases family_descends (prefixWord ++ tailWord_109628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109635 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 6]
def baseStart_109635 : Nat := 118140960795 + 109635 * 2 ^ 59
def prefixEnd_109635 : Nat := 4983230072969 + 3 ^ 40 * 109635 * 2
def baseEnd_109635 : Nat := 12510100345729730279623

theorem tailTrace_109635 : CollatzResearch.WordTrace tailWord_109635 prefixEnd_109635 12510100345729730279623 := by
  unfold tailWord_109635
  simp only [CollatzResearch.WordTrace]
  refine ⟨3998716957818594012402359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2665811305212396008268239 3998716957818594012402359)
  ·
    refine ⟨5998075436727891018603539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3998716957818594012402359 5998075436727891018603539)
    ·
      refine ⟨8997113155091836527905309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5998075436727891018603539 8997113155091836527905309)
      ·
        refine ⟨3373917433159438697964491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8997113155091836527905309 3373917433159438697964491)
        ·
          refine ⟨5060876149739158046946737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3373917433159438697964491 5060876149739158046946737)
          ·
            refine ⟨3795657112304368535210053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5060876149739158046946737 3795657112304368535210053)
            ·
              refine ⟨711685708557069100351885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3795657112304368535210053 711685708557069100351885)
              ·
                refine ⟨266882140708900912631957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 711685708557069100351885 266882140708900912631957)
                ·
                  refine ⟨12510100345729730279623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 266882140708900912631957 12510100345729730279623)
                  ·
                    rfl

theorem cell22_109635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 6].length) (baseStart_109635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109635 prefixEnd_109635 := by exact prefixLift 109635
  have htrace : WordTrace (prefixWord ++ tailWord_109635) baseStart_109635 baseEnd_109635 := by
    simpa [prefixWord, tailWord_109635, baseEnd_109635] using wordTrace_append hprefix tailTrace_109635
  have hstable : (prefixWord ++ tailWord_109635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109635).length < 2 ^ (prefixWord ++ tailWord_109635).sum := by decide
  have hdescent : baseEnd_109635 < baseStart_109635 := by decide
  rcases family_descends (prefixWord ++ tailWord_109635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109667 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 4, 3]
def baseStart_109667 : Nat := 118140960795 + 109667 * 2 ^ 59
def prefixEnd_109667 : Nat := 4983230072969 + 3 ^ 40 * 109667 * 2
def baseEnd_109667 : Nat := 37541255291151774038771

theorem tailTrace_109667 : CollatzResearch.WordTrace tailWord_109667 prefixEnd_109667 37541255291151774038771 := by
  unfold tailWord_109667
  simp only [CollatzResearch.WordTrace]
  refine ⟨3999884093702663477567255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2666589395801775651711503 3999884093702663477567255)
  ·
    refine ⟨5999826140553995216350883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3999884093702663477567255 5999826140553995216350883)
    ·
      refine ⟨8999739210830992824526325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5999826140553995216350883 8999739210830992824526325)
      ·
        refine ⟨843725551015405577299343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8999739210830992824526325 843725551015405577299343)
        ·
          refine ⟨1265588326523108365949015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843725551015405577299343 1265588326523108365949015)
          ·
            refine ⟨1898382489784662548923523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265588326523108365949015 1898382489784662548923523)
            ·
              refine ⟨2847573734676993823385285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898382489784662548923523 2847573734676993823385285)
              ·
                refine ⟨533920075251936341884741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2847573734676993823385285 533920075251936341884741)
                ·
                  refine ⟨100110014109738064103389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533920075251936341884741 100110014109738064103389)
                  ·
                    refine ⟨37541255291151774038771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100110014109738064103389 37541255291151774038771)
                    ·
                      rfl

theorem cell22_109667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 3].length) (baseStart_109667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109667 prefixEnd_109667 := by exact prefixLift 109667
  have htrace : WordTrace (prefixWord ++ tailWord_109667) baseStart_109667 baseEnd_109667 := by
    simpa [prefixWord, tailWord_109667, baseEnd_109667] using wordTrace_append hprefix tailTrace_109667
  have hstable : (prefixWord ++ tailWord_109667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109667).length < 2 ^ (prefixWord ++ tailWord_109667).sum := by decide
  have hdescent : baseEnd_109667 < baseStart_109667 := by decide
  rcases family_descends (prefixWord ++ tailWord_109667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109669 : List Nat := [1, 3, 1, 3, 2, 1, 4, 3, 4]
def baseStart_109669 : Nat := 118140960795 + 109669 * 2 ^ 59
def prefixEnd_109669 : Nat := 4983230072969 + 3 ^ 40 * 109669 * 2
def baseEnd_109669 : Nat := 12513979977341478496255

theorem tailTrace_109669 : CollatzResearch.WordTrace tailWord_109669 prefixEnd_109669 12513979977341478496255 := by
  unfold tailWord_109669
  simp only [CollatzResearch.WordTrace]
  refine ⟨3999957039695417819140061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2666638026463611879426707 3999957039695417819140061)
  ·
    refine ⟨1499983889885781682177523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3999957039695417819140061 1499983889885781682177523)
    ·
      refine ⟨2249975834828672523266285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1499983889885781682177523 2249975834828672523266285)
      ·
        refine ⟨843740938060752196224857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2249975834828672523266285 843740938060752196224857)
        ·
          refine ⟨632805703545564147168643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843740938060752196224857 632805703545564147168643)
          ·
            refine ⟨949208555318346220752965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632805703545564147168643 949208555318346220752965)
            ·
              refine ⟨177976604122189916391181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 949208555318346220752965 177976604122189916391181)
              ·
                refine ⟨66741226545821218646693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177976604122189916391181 66741226545821218646693)
                ·
                  refine ⟨12513979977341478496255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66741226545821218646693 12513979977341478496255)
                  ·
                    rfl

theorem cell22_109669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_109669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109669 prefixEnd_109669 := by exact prefixLift 109669
  have htrace : WordTrace (prefixWord ++ tailWord_109669) baseStart_109669 baseEnd_109669 := by
    simpa [prefixWord, tailWord_109669, baseEnd_109669] using wordTrace_append hprefix tailTrace_109669
  have hstable : (prefixWord ++ tailWord_109669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109669).length < 2 ^ (prefixWord ++ tailWord_109669).sum := by decide
  have hdescent : baseEnd_109669 < baseStart_109669 := by decide
  rcases family_descends (prefixWord ++ tailWord_109669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109671 : List Nat := [1, 1, 5, 1, 1, 5, 2, 1, 1, 4]
def baseStart_109671 : Nat := 118140960795 + 109671 * 2 ^ 59
def prefixEnd_109671 : Nat := 4983230072969 + 3 ^ 40 * 109671 * 2
def baseEnd_109671 : Nat := 37542624572897096938759

theorem tailTrace_109671 : CollatzResearch.WordTrace tailWord_109671 prefixEnd_109671 37542624572897096938759 := by
  unfold tailWord_109671
  simp only [CollatzResearch.WordTrace]
  refine ⟨4000029985688172160712867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2666686657125448107141911 4000029985688172160712867)
  ·
    refine ⟨6000044978532258241069301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4000029985688172160712867 6000044978532258241069301)
    ·
      refine ⟨562504216737399210100247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6000044978532258241069301 562504216737399210100247)
      ·
        refine ⟨843756325106098815150371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562504216737399210100247 843756325106098815150371)
        ·
          refine ⟨1265634487659148222725557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843756325106098815150371 1265634487659148222725557)
          ·
            refine ⟨118653233218045145880521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1265634487659148222725557 118653233218045145880521)
            ·
              refine ⟨88989924913533859410391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118653233218045145880521 88989924913533859410391)
              ·
                refine ⟨133484887370300789115587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88989924913533859410391 133484887370300789115587)
                ·
                  refine ⟨200227331055451183673381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133484887370300789115587 200227331055451183673381)
                  ·
                    refine ⟨37542624572897096938759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 200227331055451183673381 37542624572897096938759)
                    ·
                      rfl

theorem cell22_109671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_109671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109671 prefixEnd_109671 := by exact prefixLift 109671
  have htrace : WordTrace (prefixWord ++ tailWord_109671) baseStart_109671 baseEnd_109671 := by
    simpa [prefixWord, tailWord_109671, baseEnd_109671] using wordTrace_append hprefix tailTrace_109671
  have hstable : (prefixWord ++ tailWord_109671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109671).length < 2 ^ (prefixWord ++ tailWord_109671).sum := by decide
  have hdescent : baseEnd_109671 < baseStart_109671 := by decide
  rcases family_descends (prefixWord ++ tailWord_109671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109680 : List Nat := [2, 1, 1, 1, 5, 1, 11]
def baseStart_109680 : Nat := 118140960795 + 109680 * 2 ^ 59
def prefixEnd_109680 : Nat := 4983230072969 + 3 ^ 40 * 109680 * 2
def baseEnd_109680 : Nat := 1390581683586076794953

theorem tailTrace_109680 : CollatzResearch.WordTrace tailWord_109680 prefixEnd_109680 1390581683586076794953 := by
  unfold tailWord_109680
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000179121327783348895247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2666905495103711131860329 2000179121327783348895247)
  ·
    refine ⟨3000268681991675023342871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2000179121327783348895247 3000268681991675023342871)
    ·
      refine ⟨4500403022987512535014307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3000268681991675023342871 4500403022987512535014307)
      ·
        refine ⟨6750604534481268802521461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4500403022987512535014307 6750604534481268802521461)
        ·
          refine ⟨632869175107618950236387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6750604534481268802521461 632869175107618950236387)
          ·
            refine ⟨949303762661428425354581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632869175107618950236387 949303762661428425354581)
            ·
              refine ⟨1390581683586076794953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 949303762661428425354581 1390581683586076794953)
              ·
                rfl

theorem cell22_109680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 11].length) (baseStart_109680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109680 prefixEnd_109680 := by exact prefixLift 109680
  have htrace : WordTrace (prefixWord ++ tailWord_109680) baseStart_109680 baseEnd_109680 := by
    simpa [prefixWord, tailWord_109680, baseEnd_109680] using wordTrace_append hprefix tailTrace_109680
  have hstable : (prefixWord ++ tailWord_109680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109680).length < 2 ^ (prefixWord ++ tailWord_109680).sum := by decide
  have hdescent : baseEnd_109680 < baseStart_109680 := by decide
  rcases family_descends (prefixWord ++ tailWord_109680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109682 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_109682 : Nat := 118140960795 + 109682 * 2 ^ 59
def prefixEnd_109682 : Nat := 4983230072969 + 3 ^ 40 * 109682 * 2
def baseEnd_109682 : Nat := 37546390097696734913725

theorem tailTrace_109682 : CollatzResearch.WordTrace tailWord_109682 prefixEnd_109682 37546390097696734913725 := by
  unfold tailWord_109682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1000107797162080259840825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2666954125765547359575533 1000107797162080259840825)
  ·
    refine ⟨750080847871560194880619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1000107797162080259840825 750080847871560194880619)
    ·
      refine ⟨1125121271807340292320929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 750080847871560194880619 1125121271807340292320929)
      ·
        refine ⟨843840953855505219240697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1125121271807340292320929 843840953855505219240697)
        ·
          refine ⟨632880715391628914430523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843840953855505219240697 632880715391628914430523)
          ·
            refine ⟨949321073087443371645785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632880715391628914430523 949321073087443371645785)
            ·
              refine ⟨711990804815582528734339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949321073087443371645785 711990804815582528734339)
              ·
                refine ⟨1067986207223373793101509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711990804815582528734339 1067986207223373793101509)
                ·
                  refine ⟨200247413854382586206533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1067986207223373793101509 200247413854382586206533)
                  ·
                    refine ⟨37546390097696734913725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 200247413854382586206533 37546390097696734913725)
                    ·
                      rfl

theorem cell22_109682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_109682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109682 prefixEnd_109682 := by exact prefixLift 109682
  have htrace : WordTrace (prefixWord ++ tailWord_109682) baseStart_109682 baseEnd_109682 := by
    simpa [prefixWord, tailWord_109682, baseEnd_109682] using wordTrace_append hprefix tailTrace_109682
  have hstable : (prefixWord ++ tailWord_109682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109682).length < 2 ^ (prefixWord ++ tailWord_109682).sum := by decide
  have hdescent : baseEnd_109682 < baseStart_109682 := by decide
  rcases family_descends (prefixWord ++ tailWord_109682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109701 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 1, 5]
def baseStart_109701 : Nat := 118140960795 + 109701 * 2 ^ 59
def prefixEnd_109701 : Nat := 4983230072969 + 3 ^ 40 * 109701 * 2
def baseEnd_109701 : Nat := 37552894185987018688667

theorem tailTrace_109701 : CollatzResearch.WordTrace tailWord_109701 prefixEnd_109701 37552894185987018688667 := by
  unfold tailWord_109701
  simp only [CollatzResearch.WordTrace]
  refine ⟨4001124175579487284304957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2667416117052991522869971 4001124175579487284304957)
  ·
    refine ⟨1500421565842307731614359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4001124175579487284304957 1500421565842307731614359)
    ·
      refine ⟨2250632348763461597421539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500421565842307731614359 2250632348763461597421539)
      ·
        refine ⟨3375948523145192396132309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250632348763461597421539 3375948523145192396132309)
        ·
          refine ⟨79123793511215446784351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 3375948523145192396132309 79123793511215446784351)
          ·
            refine ⟨118685690266823170176527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79123793511215446784351 118685690266823170176527)
            ·
              refine ⟨178028535400234755264791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118685690266823170176527 178028535400234755264791)
              ·
                refine ⟨267042803100352132897187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178028535400234755264791 267042803100352132897187)
                ·
                  refine ⟨400564204650528199345781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267042803100352132897187 400564204650528199345781)
                  ·
                    refine ⟨37552894185987018688667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 400564204650528199345781 37552894185987018688667)
                    ·
                      rfl

theorem cell22_109701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_109701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109701 prefixEnd_109701 := by exact prefixLift 109701
  have htrace : WordTrace (prefixWord ++ tailWord_109701) baseStart_109701 baseEnd_109701 := by
    simpa [prefixWord, tailWord_109701, baseEnd_109701] using wordTrace_append hprefix tailTrace_109701
  have hstable : (prefixWord ++ tailWord_109701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109701).length < 2 ^ (prefixWord ++ tailWord_109701).sum := by decide
  have hdescent : baseEnd_109701 < baseStart_109701 := by decide
  rcases family_descends (prefixWord ++ tailWord_109701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109712 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 5, 3]
def baseStart_109712 : Nat := 118140960795 + 109712 * 2 ^ 59
def prefixEnd_109712 : Nat := 4983230072969 + 3 ^ 40 * 109712 * 2
def baseEnd_109712 : Nat := 37556659710786656663633

theorem tailTrace_109712 : CollatzResearch.WordTrace tailWord_109712 prefixEnd_109712 37556659710786656663633 := by
  unfold tailWord_109712
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000762689269818081477695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2667683585693090775303593 2000762689269818081477695)
  ·
    refine ⟨3001144033904727122216543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2000762689269818081477695 3001144033904727122216543)
    ·
      refine ⟨4501716050857090683324815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3001144033904727122216543 4501716050857090683324815)
      ·
        refine ⟨6752574076285636024987223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4501716050857090683324815 6752574076285636024987223)
        ·
          refine ⟨10128861114428454037480835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6752574076285636024987223 10128861114428454037480835)
          ·
            refine ⟨15193291671642681056221253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10128861114428454037480835 15193291671642681056221253)
            ·
              refine ⟨2848742188433002698041485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15193291671642681056221253 2848742188433002698041485)
              ·
                refine ⟨1068278320662376011765557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2848742188433002698041485 1068278320662376011765557)
                ·
                  refine ⟨100151092562097751103021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1068278320662376011765557 100151092562097751103021)
                  ·
                    refine ⟨37556659710786656663633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100151092562097751103021 37556659710786656663633)
                    ·
                      rfl

theorem cell22_109712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 5, 3].length) (baseStart_109712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109712 prefixEnd_109712 := by exact prefixLift 109712
  have htrace : WordTrace (prefixWord ++ tailWord_109712) baseStart_109712 baseEnd_109712 := by
    simpa [prefixWord, tailWord_109712, baseEnd_109712] using wordTrace_append hprefix tailTrace_109712
  have hstable : (prefixWord ++ tailWord_109712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109712).length < 2 ^ (prefixWord ++ tailWord_109712).sum := by decide
  have hdescent : baseEnd_109712 < baseStart_109712 := by decide
  rcases family_descends (prefixWord ++ tailWord_109712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109714 : List Nat := [3, 2, 3, 1, 1, 2, 4, 6]
def baseStart_109714 : Nat := 118140960795 + 109714 * 2 ^ 59
def prefixEnd_109714 : Nat := 4983230072969 + 3 ^ 40 * 109714 * 2
def baseEnd_109714 : Nat := 4173038261295479790403

theorem tailTrace_109714 : CollatzResearch.WordTrace tailWord_109714 prefixEnd_109714 4173038261295479790403 := by
  unfold tailWord_109714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1000399581133097626132049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2667732216354927003018797 1000399581133097626132049)
  ·
    refine ⟨750299685849823219599037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1000399581133097626132049 750299685849823219599037)
    ·
      refine ⟨281362382193683707349639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 750299685849823219599037 281362382193683707349639)
      ·
        refine ⟨422043573290525561024459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281362382193683707349639 422043573290525561024459)
        ·
          refine ⟨633065359935788341536689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422043573290525561024459 633065359935788341536689)
          ·
            refine ⟨474799019951841256152517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633065359935788341536689 474799019951841256152517)
            ·
              refine ⟨89024816240970235528597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 474799019951841256152517 89024816240970235528597)
              ·
                refine ⟨4173038261295479790403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89024816240970235528597 4173038261295479790403)
                ·
                  rfl

theorem cell22_109714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_109714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109714 prefixEnd_109714 := by exact prefixLift 109714
  have htrace : WordTrace (prefixWord ++ tailWord_109714) baseStart_109714 baseEnd_109714 := by
    simpa [prefixWord, tailWord_109714, baseEnd_109714] using wordTrace_append hprefix tailTrace_109714
  have hstable : (prefixWord ++ tailWord_109714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109714).length < 2 ^ (prefixWord ++ tailWord_109714).sum := by decide
  have hdescent : baseEnd_109714 < baseStart_109714 := by decide
  rcases family_descends (prefixWord ++ tailWord_109714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109746 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_109746 : Nat := 118140960795 + 109746 * 2 ^ 59
def prefixEnd_109746 : Nat := 4983230072969 + 3 ^ 40 * 109746 * 2
def baseEnd_109746 : Nat := 37568298605621901313529

theorem tailTrace_109746 : CollatzResearch.WordTrace tailWord_109746 prefixEnd_109746 37568298605621901313529 := by
  unfold tailWord_109746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1000691365104114992423273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2668510306944306646462061 1000691365104114992423273)
  ·
    refine ⟨750518523828086244317455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1000691365104114992423273 750518523828086244317455)
    ·
      refine ⟨1125777785742129366476183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 750518523828086244317455 1125777785742129366476183)
      ·
        refine ⟨1688666678613194049714275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1125777785742129366476183 1688666678613194049714275)
        ·
          refine ⟨2533000017919791074571413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1688666678613194049714275 2533000017919791074571413)
          ·
            refine ⟨118734375839990206620535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2533000017919791074571413 118734375839990206620535)
            ·
              refine ⟨178101563759985309930803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118734375839990206620535 178101563759985309930803)
              ·
                refine ⟨267152345639977964896205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178101563759985309930803 267152345639977964896205)
                ·
                  refine ⟨100182129614991736836077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267152345639977964896205 100182129614991736836077)
                  ·
                    refine ⟨37568298605621901313529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100182129614991736836077 37568298605621901313529)
                    ·
                      rfl

theorem cell22_109746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_109746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109746 prefixEnd_109746 := by exact prefixLift 109746
  have htrace : WordTrace (prefixWord ++ tailWord_109746) baseStart_109746 baseEnd_109746 := by
    simpa [prefixWord, tailWord_109746, baseEnd_109746] using wordTrace_append hprefix tailTrace_109746
  have hstable : (prefixWord ++ tailWord_109746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109746).length < 2 ^ (prefixWord ++ tailWord_109746).sum := by decide
  have hdescent : baseEnd_109746 < baseStart_109746 := by decide
  rcases family_descends (prefixWord ++ tailWord_109746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109757 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_109757 : Nat := 118140960795 + 109757 * 2 ^ 59
def prefixEnd_109757 : Nat := 4983230072969 + 3 ^ 40 * 109757 * 2
def baseEnd_109757 : Nat := 37572064130421539288495

theorem tailTrace_109757 : CollatzResearch.WordTrace tailWord_109757 prefixEnd_109757 37572064130421539288495 := by
  unfold tailWord_109757
  simp only [CollatzResearch.WordTrace]
  refine ⟨4003166663376608848343525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2668777775584405898895683 4003166663376608848343525)
  ·
    refine ⟨750593749383114159064411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4003166663376608848343525 750593749383114159064411)
    ·
      refine ⟨1125890624074671238596617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 750593749383114159064411 1125890624074671238596617)
      ·
        refine ⟨844417968056003428947463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1125890624074671238596617 844417968056003428947463)
        ·
          refine ⟨1266626952084005143421195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844417968056003428947463 1266626952084005143421195)
          ·
            refine ⟨1899940428126007715131793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266626952084005143421195 1899940428126007715131793)
            ·
              refine ⟨1424955321094505786348845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1899940428126007715131793 1424955321094505786348845)
              ·
                refine ⟨534358245410439669880817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1424955321094505786348845 534358245410439669880817)
                ·
                  refine ⟨400768684057829752410613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534358245410439669880817 400768684057829752410613)
                  ·
                    refine ⟨37572064130421539288495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 400768684057829752410613 37572064130421539288495)
                    ·
                      rfl

theorem cell22_109757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_109757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109757 prefixEnd_109757 := by exact prefixLift 109757
  have htrace : WordTrace (prefixWord ++ tailWord_109757) baseStart_109757 baseEnd_109757 := by
    simpa [prefixWord, tailWord_109757, baseEnd_109757] using wordTrace_append hprefix tailTrace_109757
  have hstable : (prefixWord ++ tailWord_109757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109757).length < 2 ^ (prefixWord ++ tailWord_109757).sum := by decide
  have hdescent : baseEnd_109757 < baseStart_109757 := by decide
  rcases family_descends (prefixWord ++ tailWord_109757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109759 : List Nat := [1, 1, 2, 2, 2, 2, 6, 1, 5]
def baseStart_109759 : Nat := 118140960795 + 109759 * 2 ^ 59
def prefixEnd_109759 : Nat := 4983230072969 + 3 ^ 40 * 109759 * 2
def baseEnd_109759 : Nat := 12524249590431400246163

theorem tailTrace_109759 : CollatzResearch.WordTrace tailWord_109759 prefixEnd_109759 12524249590431400246163 := by
  unfold tailWord_109759
  simp only [CollatzResearch.WordTrace]
  refine ⟨4003239609369363189916331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2668826406246242126610887 4003239609369363189916331)
  ·
    refine ⟨6004859414054044784874497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4003239609369363189916331 6004859414054044784874497)
    ·
      refine ⟨4503644560540533588655873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6004859414054044784874497 4503644560540533588655873)
      ·
        refine ⟨3377733420405400191491905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4503644560540533588655873 3377733420405400191491905)
        ·
          refine ⟨2533300065304050143618929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3377733420405400191491905 2533300065304050143618929)
          ·
            refine ⟨1899975048978037607714197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2533300065304050143618929 1899975048978037607714197)
            ·
              refine ⟨89061330420845512861603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1899975048978037607714197 89061330420845512861603)
              ·
                refine ⟨133591995631268269292405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89061330420845512861603 133591995631268269292405)
                ·
                  refine ⟨12524249590431400246163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133591995631268269292405 12524249590431400246163)
                  ·
                    rfl

theorem cell22_109759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 5].length) (baseStart_109759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109759 prefixEnd_109759 := by exact prefixLift 109759
  have htrace : WordTrace (prefixWord ++ tailWord_109759) baseStart_109759 baseEnd_109759 := by
    simpa [prefixWord, tailWord_109759, baseEnd_109759] using wordTrace_append hprefix tailTrace_109759
  have hstable : (prefixWord ++ tailWord_109759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109759).length < 2 ^ (prefixWord ++ tailWord_109759).sum := by decide
  have hdescent : baseEnd_109759 < baseStart_109759 := by decide
  rcases family_descends (prefixWord ++ tailWord_109759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109797 : List Nat := [1, 3, 1, 4, 4, 1, 2, 2, 1, 3]
def baseStart_109797 : Nat := 118140960795 + 109797 * 2 ^ 59
def prefixEnd_109797 : Nat := 4983230072969 + 3 ^ 40 * 109797 * 2
def baseEnd_109797 : Nat := 37585756947874768288373

theorem tailTrace_109797 : CollatzResearch.WordTrace tailWord_109797 prefixEnd_109797 37585756947874768288373 := by
  unfold tailWord_109797
  simp only [CollatzResearch.WordTrace]
  refine ⟨4004625583231695679799645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2669750388821130453199763 4004625583231695679799645)
  ·
    refine ⟨1501734593711885879924867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4004625583231695679799645 1501734593711885879924867)
    ·
      refine ⟨2252601890567828819887301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1501734593711885879924867 2252601890567828819887301)
      ·
        refine ⟨422362854481467903728869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2252601890567828819887301 422362854481467903728869)
        ·
          refine ⟨79193035215275231949163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 422362854481467903728869 79193035215275231949163)
          ·
            refine ⟨118789552822912847923745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79193035215275231949163 118789552822912847923745)
            ·
              refine ⟨89092164617184635942809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118789552822912847923745 89092164617184635942809)
              ·
                refine ⟨66819123462888476957107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89092164617184635942809 66819123462888476957107)
                ·
                  refine ⟨100228685194332715435661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66819123462888476957107 100228685194332715435661)
                  ·
                    refine ⟨37585756947874768288373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100228685194332715435661 37585756947874768288373)
                    ·
                      rfl

theorem cell22_109797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_109797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109797 prefixEnd_109797 := by exact prefixLift 109797
  have htrace : WordTrace (prefixWord ++ tailWord_109797) baseStart_109797 baseEnd_109797 := by
    simpa [prefixWord, tailWord_109797, baseEnd_109797] using wordTrace_append hprefix tailTrace_109797
  have hstable : (prefixWord ++ tailWord_109797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109797).length < 2 ^ (prefixWord ++ tailWord_109797).sum := by decide
  have hdescent : baseEnd_109797 < baseStart_109797 := by decide
  rcases family_descends (prefixWord ++ tailWord_109797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109817 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 1, 6]
def baseStart_109817 : Nat := 118140960795 + 109817 * 2 ^ 59
def prefixEnd_109817 : Nat := 4983230072969 + 3 ^ 40 * 109817 * 2
def baseEnd_109817 : Nat := 37592603356601382788311

theorem tailTrace_109817 : CollatzResearch.WordTrace tailWord_109817 prefixEnd_109817 37592603356601382788311 := by
  unfold tailWord_109817
  simp only [CollatzResearch.WordTrace]
  refine ⟨4005355043159239095527705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2670236695439492730351803 4005355043159239095527705)
  ·
    refine ⟨3004016282369429321645779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4005355043159239095527705 3004016282369429321645779)
    ·
      refine ⟨4506024423554143982468669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3004016282369429321645779 4506024423554143982468669)
      ·
        refine ⟨1689759158832803993425751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4506024423554143982468669 1689759158832803993425751)
        ·
          refine ⟨2534638738249205990138627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1689759158832803993425751 2534638738249205990138627)
          ·
            refine ⟨3801958107373808985207941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534638738249205990138627 3801958107373808985207941)
            ·
              refine ⟨712867145132589184726489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3801958107373808985207941 712867145132589184726489)
              ·
                refine ⟨534650358849441888544867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712867145132589184726489 534650358849441888544867)
                ·
                  refine ⟨801975538274162832817301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 534650358849441888544867 801975538274162832817301)
                  ·
                    refine ⟨37592603356601382788311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 801975538274162832817301 37592603356601382788311)
                    ·
                      rfl

theorem cell22_109817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_109817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109817 prefixEnd_109817 := by exact prefixLift 109817
  have htrace : WordTrace (prefixWord ++ tailWord_109817) baseStart_109817 baseEnd_109817 := by
    simpa [prefixWord, tailWord_109817, baseEnd_109817] using wordTrace_append hprefix tailTrace_109817
  have hstable : (prefixWord ++ tailWord_109817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109817).length < 2 ^ (prefixWord ++ tailWord_109817).sum := by decide
  have hdescent : baseEnd_109817 < baseStart_109817 := by decide
  rcases family_descends (prefixWord ++ tailWord_109817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109853 : List Nat := [1, 4, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_109853 : Nat := 118140960795 + 109853 * 2 ^ 59
def prefixEnd_109853 : Nat := 4983230072969 + 3 ^ 40 * 109853 * 2
def baseEnd_109853 : Nat := 37604926892309288888201

theorem tailTrace_109853 : CollatzResearch.WordTrace tailWord_109853 prefixEnd_109853 37604926892309288888201 := by
  unfold tailWord_109853
  simp only [CollatzResearch.WordTrace]
  refine ⟨4006668071028817243838213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2671112047352544829225475 4006668071028817243838213)
  ·
    refine ⟨751250263317903233219665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4006668071028817243838213 751250263317903233219665)
    ·
      refine ⟨563437697488427424914749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 751250263317903233219665 563437697488427424914749)
      ·
        refine ⟨211289136558160284343031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 563437697488427424914749 211289136558160284343031)
        ·
          refine ⟨316933704837240426514547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211289136558160284343031 316933704837240426514547)
          ·
            refine ⟨475400557255860639771821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316933704837240426514547 475400557255860639771821)
            ·
              refine ⟨178275208970947739914433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475400557255860639771821 178275208970947739914433)
              ·
                refine ⟨133706406728210804935825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178275208970947739914433 133706406728210804935825)
                ·
                  refine ⟨100279805046158103701869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133706406728210804935825 100279805046158103701869)
                  ·
                    refine ⟨37604926892309288888201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100279805046158103701869 37604926892309288888201)
                    ·
                      rfl

theorem cell22_109853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_109853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109853 prefixEnd_109853 := by exact prefixLift 109853
  have htrace : WordTrace (prefixWord ++ tailWord_109853) baseStart_109853 baseEnd_109853 := by
    simpa [prefixWord, tailWord_109853, baseEnd_109853] using wordTrace_append hprefix tailTrace_109853
  have hstable : (prefixWord ++ tailWord_109853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109853).length < 2 ^ (prefixWord ++ tailWord_109853).sum := by decide
  have hdescent : baseEnd_109853 < baseStart_109853 := by decide
  rcases family_descends (prefixWord ++ tailWord_109853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109973 : List Nat := [1, 3, 2, 1, 1, 2, 6, 2, 4]
def baseStart_109973 : Nat := 118140960795 + 109973 * 2 ^ 59
def prefixEnd_109973 : Nat := 4983230072969 + 3 ^ 40 * 109973 * 2
def baseEnd_109973 : Nat := 12548668448222991962611

theorem tailTrace_109973 : CollatzResearch.WordTrace tailWord_109973 prefixEnd_109973 12548668448222991962611 := by
  unfold tailWord_109973
  simp only [CollatzResearch.WordTrace]
  refine ⟨4011044830594077738206573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2674029887062718492137715 4011044830594077738206573)
  ·
    refine ⟨1504141811472779151827465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4011044830594077738206573 1504141811472779151827465)
    ·
      refine ⟨1128106358604584363870599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1504141811472779151827465 1128106358604584363870599)
      ·
        refine ⟨1692159537906876545805899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1128106358604584363870599 1692159537906876545805899)
        ·
          refine ⟨2538239306860314818708849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692159537906876545805899 2538239306860314818708849)
          ·
            refine ⟨1903679480145236114031637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2538239306860314818708849 1903679480145236114031637)
            ·
              refine ⟨89234975631807942845233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1903679480145236114031637 89234975631807942845233)
              ·
                refine ⟨66926231723855957133925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89234975631807942845233 66926231723855957133925)
                ·
                  refine ⟨12548668448222991962611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66926231723855957133925 12548668448222991962611)
                  ·
                    rfl

theorem cell22_109973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_109973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_109973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_109973 prefixEnd_109973 := by exact prefixLift 109973
  have htrace : WordTrace (prefixWord ++ tailWord_109973) baseStart_109973 baseEnd_109973 := by
    simpa [prefixWord, tailWord_109973, baseEnd_109973] using wordTrace_append hprefix tailTrace_109973
  have hstable : (prefixWord ++ tailWord_109973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109973).length < 2 ^ (prefixWord ++ tailWord_109973).sum := by decide
  have hdescent : baseEnd_109973 < baseStart_109973 := by decide
  rcases family_descends (prefixWord ++ tailWord_109973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110001 : List Nat := [1, 2, 2, 4, 1, 1, 5, 6]
def baseStart_110001 : Nat := 118140960795 + 110001 * 2 ^ 59
def prefixEnd_110001 : Nat := 4983230072969 + 3 ^ 40 * 110001 * 2
def baseEnd_110001 : Nat := 4183954479654026243083

theorem tailTrace_110001 : CollatzResearch.WordTrace tailWord_110001 prefixEnd_110001 4183954479654026243083 := by
  unfold tailWord_110001
  simp only [CollatzResearch.WordTrace]
  refine ⟨4012066074492638520225857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2674710716328425680150571 4012066074492638520225857)
  ·
    refine ⟨3009049555869478890169393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4012066074492638520225857 3009049555869478890169393)
    ·
      refine ⟨2256787166902109167627045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3009049555869478890169393 2256787166902109167627045)
      ·
        refine ⟨423147593794145468930071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2256787166902109167627045 423147593794145468930071)
        ·
          refine ⟨634721390691218203395107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423147593794145468930071 634721390691218203395107)
          ·
            refine ⟨952082086036827305092661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634721390691218203395107 952082086036827305092661)
            ·
              refine ⟨89257695565952559852437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 952082086036827305092661 89257695565952559852437)
              ·
                refine ⟨4183954479654026243083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89257695565952559852437 4183954479654026243083)
                ·
                  rfl

theorem cell22_110001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 6].length) (baseStart_110001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110001 prefixEnd_110001 := by exact prefixLift 110001
  have htrace : WordTrace (prefixWord ++ tailWord_110001) baseStart_110001 baseEnd_110001 := by
    simpa [prefixWord, tailWord_110001, baseEnd_110001] using wordTrace_append hprefix tailTrace_110001
  have hstable : (prefixWord ++ tailWord_110001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110001).length < 2 ^ (prefixWord ++ tailWord_110001).sum := by decide
  have hdescent : baseEnd_110001 < baseStart_110001 := by decide
  rcases family_descends (prefixWord ++ tailWord_110001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110084 : List Nat := [2, 3, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_110084 : Nat := 118140960795 + 110084 * 2 ^ 59
def prefixEnd_110084 : Nat := 4983230072969 + 3 ^ 40 * 110084 * 2
def baseEnd_110084 : Nat := 37684002913101686362493

theorem tailTrace_110084 : CollatzResearch.WordTrace tailWord_110084 prefixEnd_110084 37684002913101686362493 := by
  unfold tailWord_110084
  simp only [CollatzResearch.WordTrace]
  refine ⟨2007546666595971847748653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2676728888794629130331537 2007546666595971847748653)
  ·
    refine ⟨752829999973489442905745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2007546666595971847748653 752829999973489442905745)
    ·
      refine ⟨564622499980117082179309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 752829999973489442905745 564622499980117082179309)
      ·
        refine ⟨211733437492543905817241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564622499980117082179309 211733437492543905817241)
        ·
          refine ⟨158800078119407929362931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211733437492543905817241 158800078119407929362931)
          ·
            refine ⟨238200117179111894044397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158800078119407929362931 238200117179111894044397)
            ·
              refine ⟨89325043942166960266649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238200117179111894044397 89325043942166960266649)
              ·
                refine ⟨66993782956625220199987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89325043942166960266649 66993782956625220199987)
                ·
                  refine ⟨100490674434937830299981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66993782956625220199987 100490674434937830299981)
                  ·
                    refine ⟨37684002913101686362493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100490674434937830299981 37684002913101686362493)
                    ·
                      rfl

theorem cell22_110084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_110084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110084 prefixEnd_110084 := by exact prefixLift 110084
  have htrace : WordTrace (prefixWord ++ tailWord_110084) baseStart_110084 baseEnd_110084 := by
    simpa [prefixWord, tailWord_110084, baseEnd_110084] using wordTrace_append hprefix tailTrace_110084
  have hstable : (prefixWord ++ tailWord_110084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110084).length < 2 ^ (prefixWord ++ tailWord_110084).sum := by decide
  have hdescent : baseEnd_110084 < baseStart_110084 := by decide
  rcases family_descends (prefixWord ++ tailWord_110084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110106 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_110106 : Nat := 118140960795 + 110106 * 2 ^ 59
def prefixEnd_110106 : Nat := 4983230072969 + 3 ^ 40 * 110106 * 2
def baseEnd_110106 : Nat := 37691533962700962312425

theorem tailTrace_110106 : CollatzResearch.WordTrace tailWord_110106 prefixEnd_110106 37691533962700962312425 := by
  unfold tailWord_110106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1003973934778060363199543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2677263826074827635198781 1003973934778060363199543)
  ·
    refine ⟨1505960902167090544799315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1003973934778060363199543 1505960902167090544799315)
    ·
      refine ⟨2258941353250635817198973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1505960902167090544799315 2258941353250635817198973)
      ·
        refine ⟨847103007468988431449615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2258941353250635817198973 847103007468988431449615)
        ·
          refine ⟨1270654511203482647174423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847103007468988431449615 1270654511203482647174423)
          ·
            refine ⟨1905981766805223970761635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270654511203482647174423 1905981766805223970761635)
            ·
              refine ⟨2858972650207835956142453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905981766805223970761635 2858972650207835956142453)
              ·
                refine ⟨268028685956984620888355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2858972650207835956142453 268028685956984620888355)
                ·
                  refine ⟨402043028935476931332533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268028685956984620888355 402043028935476931332533)
                  ·
                    refine ⟨37691533962700962312425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 402043028935476931332533 37691533962700962312425)
                    ·
                      rfl

theorem cell22_110106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_110106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110106 prefixEnd_110106 := by exact prefixLift 110106
  have htrace : WordTrace (prefixWord ++ tailWord_110106) baseStart_110106 baseEnd_110106 := by
    simpa [prefixWord, tailWord_110106, baseEnd_110106] using wordTrace_append hprefix tailTrace_110106
  have hstable : (prefixWord ++ tailWord_110106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110106).length < 2 ^ (prefixWord ++ tailWord_110106).sum := by decide
  have hdescent : baseEnd_110106 < baseStart_110106 := by decide
  rcases family_descends (prefixWord ++ tailWord_110106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110185 : List Nat := [1, 2, 1, 1, 1, 4, 3, 5, 1, 3]
def baseStart_110185 : Nat := 118140960795 + 110185 * 2 ^ 59
def prefixEnd_110185 : Nat := 4983230072969 + 3 ^ 40 * 110185 * 2
def baseEnd_110185 : Nat := 37718577277171089587183

theorem tailTrace_110185 : CollatzResearch.WordTrace tailWord_110185 prefixEnd_110185 37718577277171089587183 := by
  unfold tailWord_110185
  simp only [CollatzResearch.WordTrace]
  refine ⟨4018777105826037944924009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2679184737217358629949339 4018777105826037944924009)
  ·
    refine ⟨3014082829369528458693007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4018777105826037944924009 3014082829369528458693007)
    ·
      refine ⟨4521124244054292688039511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3014082829369528458693007 4521124244054292688039511)
      ·
        refine ⟨6781686366081439032059267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521124244054292688039511 6781686366081439032059267)
        ·
          refine ⟨10172529549122158548088901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6781686366081439032059267 10172529549122158548088901)
          ·
            refine ⟨1907349290460404727766669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10172529549122158548088901 1907349290460404727766669)
            ·
              refine ⟨715255983922651772912501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1907349290460404727766669 715255983922651772912501)
              ·
                refine ⟨67055248492748603710547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 715255983922651772912501 67055248492748603710547)
                ·
                  refine ⟨100582872739122905565821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67055248492748603710547 100582872739122905565821)
                  ·
                    refine ⟨37718577277171089587183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100582872739122905565821 37718577277171089587183)
                    ·
                      rfl

theorem cell22_110185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 5, 1, 3].length) (baseStart_110185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110185 prefixEnd_110185 := by exact prefixLift 110185
  have htrace : WordTrace (prefixWord ++ tailWord_110185) baseStart_110185 baseEnd_110185 := by
    simpa [prefixWord, tailWord_110185, baseEnd_110185] using wordTrace_append hprefix tailTrace_110185
  have hstable : (prefixWord ++ tailWord_110185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110185).length < 2 ^ (prefixWord ++ tailWord_110185).sum := by decide
  have hdescent : baseEnd_110185 < baseStart_110185 := by decide
  rcases family_descends (prefixWord ++ tailWord_110185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110215 : List Nat := [1, 1, 4, 2, 1, 4, 3, 1, 5]
def baseStart_110215 : Nat := 118140960795 + 110215 * 2 ^ 59
def prefixEnd_110215 : Nat := 4983230072969 + 3 ^ 40 * 110215 * 2
def baseEnd_110215 : Nat := 12576282296753670445697

theorem tailTrace_110215 : CollatzResearch.WordTrace tailWord_110215 prefixEnd_110215 12576282296753670445697 := by
  unfold tailWord_110215
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019871295717353068516099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2679914197144902045677399 4019871295717353068516099)
  ·
    refine ⟨6029806943576029602774149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4019871295717353068516099 6029806943576029602774149)
    ·
      refine ⟨1130588801920505550520153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6029806943576029602774149 1130588801920505550520153)
      ·
        refine ⟨847941601440379162890115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1130588801920505550520153 847941601440379162890115)
        ·
          refine ⟨1271912402160568744335173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847941601440379162890115 1271912402160568744335173)
          ·
            refine ⟨238483575405106639562845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1271912402160568744335173 238483575405106639562845)
            ·
              refine ⟨89431340776914989836067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238483575405106639562845 89431340776914989836067)
              ·
                refine ⟨134147011165372484754101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89431340776914989836067 134147011165372484754101)
                ·
                  refine ⟨12576282296753670445697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134147011165372484754101 12576282296753670445697)
                  ·
                    rfl

theorem cell22_110215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 5].length) (baseStart_110215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110215 prefixEnd_110215 := by exact prefixLift 110215
  have htrace : WordTrace (prefixWord ++ tailWord_110215) baseStart_110215 baseEnd_110215 := by
    simpa [prefixWord, tailWord_110215, baseEnd_110215] using wordTrace_append hprefix tailTrace_110215
  have hstable : (prefixWord ++ tailWord_110215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110215).length < 2 ^ (prefixWord ++ tailWord_110215).sum := by decide
  have hdescent : baseEnd_110215 < baseStart_110215 := by decide
  rcases family_descends (prefixWord ++ tailWord_110215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110236 : List Nat := [2, 2, 3, 2, 4, 1, 1, 3, 1, 3]
def baseStart_110236 : Nat := 118140960795 + 110236 * 2 ^ 59
def prefixEnd_110236 : Nat := 4983230072969 + 3 ^ 40 * 110236 * 2
def baseEnd_110236 : Nat := 37736035619423956562027

theorem tailTrace_110236 : CollatzResearch.WordTrace tailWord_110236 prefixEnd_110236 37736035619423956562027 := by
  unfold tailWord_110236
  simp only [CollatzResearch.WordTrace]
  refine ⟨2010318614320636827515281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2680424819094182436687041 2010318614320636827515281)
  ·
    refine ⟨1507738960740477620636461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2010318614320636827515281 1507738960740477620636461)
    ·
      refine ⟨565402110277679107738673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1507738960740477620636461 565402110277679107738673)
      ·
        refine ⟨424051582708259330804005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565402110277679107738673 424051582708259330804005)
        ·
          refine ⟨79509671757798624525751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 424051582708259330804005 79509671757798624525751)
          ·
            refine ⟨119264507636697936788627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79509671757798624525751 119264507636697936788627)
            ·
              refine ⟨178896761455046905182941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119264507636697936788627 178896761455046905182941)
              ·
                refine ⟨67086285545642589443603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178896761455046905182941 67086285545642589443603)
                ·
                  refine ⟨100629428318463884165405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67086285545642589443603 100629428318463884165405)
                  ·
                    refine ⟨37736035619423956562027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100629428318463884165405 37736035619423956562027)
                    ·
                      rfl

theorem cell22_110236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_110236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110236 prefixEnd_110236 := by exact prefixLift 110236
  have htrace : WordTrace (prefixWord ++ tailWord_110236) baseStart_110236 baseEnd_110236 := by
    simpa [prefixWord, tailWord_110236, baseEnd_110236] using wordTrace_append hprefix tailTrace_110236
  have hstable : (prefixWord ++ tailWord_110236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110236).length < 2 ^ (prefixWord ++ tailWord_110236).sum := by decide
  have hdescent : baseEnd_110236 < baseStart_110236 := by decide
  rcases family_descends (prefixWord ++ tailWord_110236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110290 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_110290 : Nat := 118140960795 + 110290 * 2 ^ 59
def prefixEnd_110290 : Nat := 4983230072969 + 3 ^ 40 * 110290 * 2
def baseEnd_110290 : Nat := 37754520922985815711861

theorem tailTrace_110290 : CollatzResearch.WordTrace tailWord_110290 prefixEnd_110290 37754520922985815711861 := by
  unfold tailWord_110290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1005651692611410219374081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2681737846963760584997549 1005651692611410219374081)
  ·
    refine ⟨754238769458557664530561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1005651692611410219374081 754238769458557664530561)
    ·
      refine ⟨565679077093918248397921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 754238769458557664530561 565679077093918248397921)
      ·
        refine ⟨424259307820438686298441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565679077093918248397921 424259307820438686298441)
        ·
          refine ⟨318194480865329014723831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424259307820438686298441 318194480865329014723831)
          ·
            refine ⟨477291721297993522085747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318194480865329014723831 477291721297993522085747)
            ·
              refine ⟨715937581946990283128621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477291721297993522085747 715937581946990283128621)
              ·
                refine ⟨268476593230121356173233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 715937581946990283128621 268476593230121356173233)
                ·
                  refine ⟨201357444922591017129925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268476593230121356173233 201357444922591017129925)
                  ·
                    refine ⟨37754520922985815711861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201357444922591017129925 37754520922985815711861)
                    ·
                      rfl

theorem cell22_110290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_110290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110290 prefixEnd_110290 := by exact prefixLift 110290
  have htrace : WordTrace (prefixWord ++ tailWord_110290) baseStart_110290 baseEnd_110290 := by
    simpa [prefixWord, tailWord_110290, baseEnd_110290] using wordTrace_append hprefix tailTrace_110290
  have hstable : (prefixWord ++ tailWord_110290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110290).length < 2 ^ (prefixWord ++ tailWord_110290).sum := by decide
  have hdescent : baseEnd_110290 < baseStart_110290 := by decide
  rcases family_descends (prefixWord ++ tailWord_110290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110311 : List Nat := [1, 1, 5, 4, 1, 2, 2, 2, 4]
def baseStart_110311 : Nat := 118140960795 + 110311 * 2 ^ 59
def prefixEnd_110311 : Nat := 4983230072969 + 3 ^ 40 * 110311 * 2
def baseEnd_110311 : Nat := 12587236550716253645599

theorem tailTrace_110311 : CollatzResearch.WordTrace tailWord_110311 prefixEnd_110311 12587236550716253645599 := by
  unfold tailWord_110311
  simp only [CollatzResearch.WordTrace]
  refine ⟨4023372703369561464010787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2682248468913040976007191 4023372703369561464010787)
  ·
    refine ⟨6035059055054342196016181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4023372703369561464010787 6035059055054342196016181)
    ·
      refine ⟨565786786411344580876517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6035059055054342196016181 565786786411344580876517)
      ·
        refine ⟨106085022452127108914347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 565786786411344580876517 106085022452127108914347)
        ·
          refine ⟨159127533678190663371521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106085022452127108914347 159127533678190663371521)
          ·
            refine ⟨119345650258642997528641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159127533678190663371521 119345650258642997528641)
            ·
              refine ⟨89509237693982248146481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119345650258642997528641 89509237693982248146481)
              ·
                refine ⟨67131928270486686109861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89509237693982248146481 67131928270486686109861)
                ·
                  refine ⟨12587236550716253645599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67131928270486686109861 12587236550716253645599)
                  ·
                    rfl

theorem cell22_110311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 4].length) (baseStart_110311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110311 prefixEnd_110311 := by exact prefixLift 110311
  have htrace : WordTrace (prefixWord ++ tailWord_110311) baseStart_110311 baseEnd_110311 := by
    simpa [prefixWord, tailWord_110311, baseEnd_110311] using wordTrace_append hprefix tailTrace_110311
  have hstable : (prefixWord ++ tailWord_110311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110311).length < 2 ^ (prefixWord ++ tailWord_110311).sum := by decide
  have hdescent : baseEnd_110311 < baseStart_110311 := by decide
  rcases family_descends (prefixWord ++ tailWord_110311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110318 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_110318 : Nat := 118140960795 + 110318 * 2 ^ 59
def prefixEnd_110318 : Nat := 4983230072969 + 3 ^ 40 * 110318 * 2
def baseEnd_110318 : Nat := 37764105895203076011775

theorem tailTrace_110318 : CollatzResearch.WordTrace tailWord_110318 prefixEnd_110318 37764105895203076011775 := by
  unfold tailWord_110318
  simp only [CollatzResearch.WordTrace]
  refine ⟨502953501793025207439451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2682418676229467773010405 502953501793025207439451)
  ·
    refine ⟨754430252689537811159177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 502953501793025207439451 754430252689537811159177)
    ·
      refine ⟨565822689517153358369383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 754430252689537811159177 565822689517153358369383)
      ·
        refine ⟨848734034275730037554075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565822689517153358369383 848734034275730037554075)
        ·
          refine ⟨1273101051413595056331113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848734034275730037554075 1273101051413595056331113)
          ·
            refine ⟨954825788560196292248335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1273101051413595056331113 954825788560196292248335)
            ·
              refine ⟨1432238682840294438372503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954825788560196292248335 1432238682840294438372503)
              ·
                refine ⟨2148358024260441657558755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432238682840294438372503 2148358024260441657558755)
                ·
                  refine ⟨3222537036390662486338133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148358024260441657558755 3222537036390662486338133)
                  ·
                    refine ⟨37764105895203076011775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3222537036390662486338133 37764105895203076011775)
                    ·
                      rfl

theorem cell22_110318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_110318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110318 prefixEnd_110318 := by exact prefixLift 110318
  have htrace : WordTrace (prefixWord ++ tailWord_110318) baseStart_110318 baseEnd_110318 := by
    simpa [prefixWord, tailWord_110318, baseEnd_110318] using wordTrace_append hprefix tailTrace_110318
  have hstable : (prefixWord ++ tailWord_110318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110318).length < 2 ^ (prefixWord ++ tailWord_110318).sum := by decide
  have hdescent : baseEnd_110318 < baseStart_110318 := by decide
  rcases family_descends (prefixWord ++ tailWord_110318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110397 : List Nat := [1, 4, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_110397 : Nat := 118140960795 + 110397 * 2 ^ 59
def prefixEnd_110397 : Nat := 4983230072969 + 3 ^ 40 * 110397 * 2
def baseEnd_110397 : Nat := 37791149209673203286533

theorem tailTrace_110397 : CollatzResearch.WordTrace tailWord_110397 prefixEnd_110397 37791149209673203286533 := by
  unfold tailWord_110397
  simp only [CollatzResearch.WordTrace]
  refine ⟨4026509381057998151641445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2684339587371998767760963 4026509381057998151641445)
  ·
    refine ⟨754970508948374653432771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4026509381057998151641445 754970508948374653432771)
    ·
      refine ⟨1132455763422561980149157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754970508948374653432771 1132455763422561980149157)
      ·
        refine ⟨212335455641730371277967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1132455763422561980149157 212335455641730371277967)
        ·
          refine ⟨318503183462595556916951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212335455641730371277967 318503183462595556916951)
          ·
            refine ⟨477754775193893335375427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318503183462595556916951 477754775193893335375427)
            ·
              refine ⟨716632162790840003063141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477754775193893335375427 716632162790840003063141)
              ·
                refine ⟨134368530523282500574339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 716632162790840003063141 134368530523282500574339)
                ·
                  refine ⟨201552795784923750861509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134368530523282500574339 201552795784923750861509)
                  ·
                    refine ⟨37791149209673203286533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201552795784923750861509 37791149209673203286533)
                    ·
                      rfl

theorem cell22_110397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_110397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110397 prefixEnd_110397 := by exact prefixLift 110397
  have htrace : WordTrace (prefixWord ++ tailWord_110397) baseStart_110397 baseEnd_110397 := by
    simpa [prefixWord, tailWord_110397, baseEnd_110397] using wordTrace_append hprefix tailTrace_110397
  have hstable : (prefixWord ++ tailWord_110397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110397).length < 2 ^ (prefixWord ++ tailWord_110397).sum := by decide
  have hdescent : baseEnd_110397 < baseStart_110397 := by decide
  rcases family_descends (prefixWord ++ tailWord_110397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110410 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 6, 3]
def baseStart_110410 : Nat := 118140960795 + 110410 * 2 ^ 59
def prefixEnd_110410 : Nat := 4983230072969 + 3 ^ 40 * 110410 * 2
def baseEnd_110410 : Nat := 37795599375345502711493

theorem tailTrace_110410 : CollatzResearch.WordTrace tailWord_110410 prefixEnd_110410 37795599375345502711493 := by
  unfold tailWord_110410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1006745882502725342966171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2684655686673934247909789 1006745882502725342966171)
  ·
    refine ⟨1510118823754088014449257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1006745882502725342966171 1510118823754088014449257)
    ·
      refine ⟨1132589117815566010836943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1510118823754088014449257 1132589117815566010836943)
      ·
        refine ⟨1698883676723349016255415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1132589117815566010836943 1698883676723349016255415)
        ·
          refine ⟨2548325515085023524383123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1698883676723349016255415 2548325515085023524383123)
          ·
            refine ⟨3822488272627535286574685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548325515085023524383123 3822488272627535286574685)
            ·
              refine ⟨1433433102235325732465507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3822488272627535286574685 1433433102235325732465507)
              ·
                refine ⟨2150149653352988598698261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433433102235325732465507 2150149653352988598698261)
                ·
                  refine ⟨100788265000921340563981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2150149653352988598698261 100788265000921340563981)
                  ·
                    refine ⟨37795599375345502711493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100788265000921340563981 37795599375345502711493)
                    ·
                      rfl

theorem cell22_110410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_110410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110410 prefixEnd_110410 := by exact prefixLift 110410
  have htrace : WordTrace (prefixWord ++ tailWord_110410) baseStart_110410 baseEnd_110410 := by
    simpa [prefixWord, tailWord_110410, baseEnd_110410] using wordTrace_append hprefix tailTrace_110410
  have hstable : (prefixWord ++ tailWord_110410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110410).length < 2 ^ (prefixWord ++ tailWord_110410).sum := by decide
  have hdescent : baseEnd_110410 < baseStart_110410 := by decide
  rcases family_descends (prefixWord ++ tailWord_110410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110425 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 2, 4]
def baseStart_110425 : Nat := 118140960795 + 110425 * 2 ^ 59
def prefixEnd_110425 : Nat := 4983230072969 + 3 ^ 40 * 110425 * 2
def baseEnd_110425 : Nat := 37800734181890463586447

theorem tailTrace_110425 : CollatzResearch.WordTrace tailWord_110425 prefixEnd_110425 37800734181890463586447 := by
  unfold tailWord_110425
  simp only [CollatzResearch.WordTrace]
  refine ⟨4027530624956558933660729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2685020416637705955773819 4027530624956558933660729)
  ·
    refine ⟨3020647968717419200245547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4027530624956558933660729 3020647968717419200245547)
    ·
      refine ⟨4530971953076128800368321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020647968717419200245547 4530971953076128800368321)
      ·
        refine ⟨3398228964807096600276241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4530971953076128800368321 3398228964807096600276241)
        ·
          refine ⟨2548671723605322450207181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3398228964807096600276241 2548671723605322450207181)
          ·
            refine ⟨955751896351995918827693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2548671723605322450207181 955751896351995918827693)
            ·
              refine ⟨358406961131998469560385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 955751896351995918827693 358406961131998469560385)
              ·
                refine ⟨268805220848998852170289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 358406961131998469560385 268805220848998852170289)
                ·
                  refine ⟨201603915636749139127717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 268805220848998852170289 201603915636749139127717)
                  ·
                    refine ⟨37800734181890463586447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201603915636749139127717 37800734181890463586447)
                    ·
                      rfl

theorem cell22_110425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_110425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110425 prefixEnd_110425 := by exact prefixLift 110425
  have htrace : WordTrace (prefixWord ++ tailWord_110425) baseStart_110425 baseEnd_110425 := by
    simpa [prefixWord, tailWord_110425, baseEnd_110425] using wordTrace_append hprefix tailTrace_110425
  have hstable : (prefixWord ++ tailWord_110425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110425).length < 2 ^ (prefixWord ++ tailWord_110425).sum := by decide
  have hdescent : baseEnd_110425 < baseStart_110425 := by decide
  rcases family_descends (prefixWord ++ tailWord_110425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110440 : List Nat := [2, 1, 4, 2, 1, 1, 4, 7]
def baseStart_110440 : Nat := 118140960795 + 110440 * 2 ^ 59
def prefixEnd_110440 : Nat := 4983230072969 + 3 ^ 40 * 110440 * 2
def baseEnd_110440 : Nat := 4200652109826158273489

theorem tailTrace_110440 : CollatzResearch.WordTrace tailWord_110440 prefixEnd_110440 4200652109826158273489 := by
  unfold tailWord_110440
  simp only [CollatzResearch.WordTrace]
  refine ⟨2014038859951108247728387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2685385146601477663637849 2014038859951108247728387)
  ·
    refine ⟨3021058289926662371592581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2014038859951108247728387 3021058289926662371592581)
    ·
      refine ⟨566448429361249194673609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3021058289926662371592581 566448429361249194673609)
      ·
        refine ⟨424836322020936896005207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566448429361249194673609 424836322020936896005207)
        ·
          refine ⟨637254483031405344007811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424836322020936896005207 637254483031405344007811)
          ·
            refine ⟨955881724547108016011717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637254483031405344007811 955881724547108016011717)
            ·
              refine ⟨179227823352582753002197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 955881724547108016011717 179227823352582753002197)
              ·
                refine ⟨4200652109826158273489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 179227823352582753002197 4200652109826158273489)
                ·
                  rfl

theorem cell22_110440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 7].length) (baseStart_110440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110440 prefixEnd_110440 := by exact prefixLift 110440
  have htrace : WordTrace (prefixWord ++ tailWord_110440) baseStart_110440 baseEnd_110440 := by
    simpa [prefixWord, tailWord_110440, baseEnd_110440] using wordTrace_append hprefix tailTrace_110440
  have hstable : (prefixWord ++ tailWord_110440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110440).length < 2 ^ (prefixWord ++ tailWord_110440).sum := by decide
  have hdescent : baseEnd_110440 < baseStart_110440 := by decide
  rcases family_descends (prefixWord ++ tailWord_110440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110444 : List Nat := [2, 2, 1, 1, 4, 2, 4, 1, 2, 3]
def baseStart_110444 : Nat := 118140960795 + 110444 * 2 ^ 59
def prefixEnd_110444 : Nat := 4983230072969 + 3 ^ 40 * 110444 * 2
def baseEnd_110444 : Nat := 37807238270180747361389

theorem tailTrace_110444 : CollatzResearch.WordTrace tailWord_110444 prefixEnd_110444 37807238270180747361389 := by
  unfold tailWord_110444
  simp only [CollatzResearch.WordTrace]
  refine ⟨2014111805943862589301193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2685482407925150119068257 2014111805943862589301193)
  ·
    refine ⟨1510583854457896941975895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2014111805943862589301193 1510583854457896941975895)
    ·
      refine ⟨2265875781686845412963843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1510583854457896941975895 2265875781686845412963843)
      ·
        refine ⟨3398813672530268119445765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2265875781686845412963843 3398813672530268119445765)
        ·
          refine ⟨637277563599425272396081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3398813672530268119445765 637277563599425272396081)
          ·
            refine ⟨477958172699568954297061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637277563599425272396081 477958172699568954297061)
            ·
              refine ⟨89617157381169178930699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 477958172699568954297061 89617157381169178930699)
              ·
                refine ⟨134425736071753768396049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89617157381169178930699 134425736071753768396049)
                ·
                  refine ⟨100819302053815326297037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134425736071753768396049 100819302053815326297037)
                  ·
                    refine ⟨37807238270180747361389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100819302053815326297037 37807238270180747361389)
                    ·
                      rfl

theorem cell22_110444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_110444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110444 prefixEnd_110444 := by exact prefixLift 110444
  have htrace : WordTrace (prefixWord ++ tailWord_110444) baseStart_110444 baseEnd_110444 := by
    simpa [prefixWord, tailWord_110444, baseEnd_110444] using wordTrace_append hprefix tailTrace_110444
  have hstable : (prefixWord ++ tailWord_110444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110444).length < 2 ^ (prefixWord ++ tailWord_110444).sum := by decide
  have hdescent : baseEnd_110444 < baseStart_110444 := by decide
  rcases family_descends (prefixWord ++ tailWord_110444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110500 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_110500 : Nat := 118140960795 + 110500 * 2 ^ 59
def prefixEnd_110500 : Nat := 4983230072969 + 3 ^ 40 * 110500 * 2
def baseEnd_110500 : Nat := 37826408214615267961217

theorem tailTrace_110500 : CollatzResearch.WordTrace tailWord_110500 prefixEnd_110500 37826408214615267961217 := by
  unfold tailWord_110500
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015133049842423371320477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2686844066456564495093969 2015133049842423371320477)
  ·
    refine ⟨755674893690908764245179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2015133049842423371320477 755674893690908764245179)
    ·
      refine ⟨1133512340536363146367769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 755674893690908764245179 1133512340536363146367769)
      ·
        refine ⟨850134255402272359775827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1133512340536363146367769 850134255402272359775827)
        ·
          refine ⟨1275201383103408539663741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850134255402272359775827 1275201383103408539663741)
          ·
            refine ⟨478200518663778202373903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1275201383103408539663741 478200518663778202373903)
            ·
              refine ⟨717300777995667303560855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478200518663778202373903 717300777995667303560855)
              ·
                refine ⟨1075951166993500955341283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717300777995667303560855 1075951166993500955341283)
                ·
                  refine ⟨1613926750490251433011925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1075951166993500955341283 1613926750490251433011925)
                  ·
                    refine ⟨37826408214615267961217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1613926750490251433011925 37826408214615267961217)
                    ·
                      rfl

theorem cell22_110500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_110500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110500 prefixEnd_110500 := by exact prefixLift 110500
  have htrace : WordTrace (prefixWord ++ tailWord_110500) baseStart_110500 baseEnd_110500 := by
    simpa [prefixWord, tailWord_110500, baseEnd_110500] using wordTrace_append hprefix tailTrace_110500
  have hstable : (prefixWord ++ tailWord_110500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110500).length < 2 ^ (prefixWord ++ tailWord_110500).sum := by decide
  have hdescent : baseEnd_110500 < baseStart_110500 := by decide
  rcases family_descends (prefixWord ++ tailWord_110500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110510 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 2, 4]
def baseStart_110510 : Nat := 118140960795 + 110510 * 2 ^ 59
def prefixEnd_110510 : Nat := 4983230072969 + 3 ^ 40 * 110510 * 2
def baseEnd_110510 : Nat := 37829831418978575211187

theorem tailTrace_110510 : CollatzResearch.WordTrace tailWord_110510 prefixEnd_110510 37829831418978575211187 := by
  unfold tailWord_110510
  simp only [CollatzResearch.WordTrace]
  refine ⟨503828853706077306313123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2687087219765745633669989 503828853706077306313123)
  ·
    refine ⟨755743280559115959469685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 503828853706077306313123 755743280559115959469685)
    ·
      refine ⟨70850932552417121200283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 755743280559115959469685 70850932552417121200283)
      ·
        refine ⟨106276398828625681800425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70850932552417121200283 106276398828625681800425)
        ·
          refine ⟨79707299121469261350319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106276398828625681800425 79707299121469261350319)
          ·
            refine ⟨119560948682203892025479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79707299121469261350319 119560948682203892025479)
            ·
              refine ⟨179341423023305838038219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119560948682203892025479 179341423023305838038219)
              ·
                refine ⟨269012134534958757057329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179341423023305838038219 269012134534958757057329)
                ·
                  refine ⟨201759100901219067792997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269012134534958757057329 201759100901219067792997)
                  ·
                    refine ⟨37829831418978575211187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201759100901219067792997 37829831418978575211187)
                    ·
                      rfl

theorem cell22_110510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_110510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110510 prefixEnd_110510 := by exact prefixLift 110510
  have htrace : WordTrace (prefixWord ++ tailWord_110510) baseStart_110510 baseEnd_110510 := by
    simpa [prefixWord, tailWord_110510, baseEnd_110510] using wordTrace_append hprefix tailTrace_110510
  have hstable : (prefixWord ++ tailWord_110510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110510).length < 2 ^ (prefixWord ++ tailWord_110510).sum := by decide
  have hdescent : baseEnd_110510 < baseStart_110510 := by decide
  rcases family_descends (prefixWord ++ tailWord_110510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110515 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 3, 4]
def baseStart_110515 : Nat := 118140960795 + 110515 * 2 ^ 59
def prefixEnd_110515 : Nat := 4983230072969 + 3 ^ 40 * 110515 * 2
def baseEnd_110515 : Nat := 37831543021160228836171

theorem tailTrace_110515 : CollatzResearch.WordTrace tailWord_110515 prefixEnd_110515 37831543021160228836171 := by
  unfold tailWord_110515
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030813194630504304436999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2687208796420336202957999 4030813194630504304436999)
  ·
    refine ⟨6046219791945756456655499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4030813194630504304436999 6046219791945756456655499)
    ·
      refine ⟨9069329687918634684983249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6046219791945756456655499 9069329687918634684983249)
      ·
        refine ⟨6801997265938976013737437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9069329687918634684983249 6801997265938976013737437)
        ·
          refine ⟨2550748974727116005151539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6801997265938976013737437 2550748974727116005151539)
          ·
            refine ⟨3826123462090674007727309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550748974727116005151539 3826123462090674007727309)
            ·
              refine ⟨1434796298284002752897741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3826123462090674007727309 1434796298284002752897741)
              ·
                refine ⟨538048611856501032336653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1434796298284002752897741 538048611856501032336653)
                ·
                  refine ⟨201768229446187887126245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538048611856501032336653 201768229446187887126245)
                  ·
                    refine ⟨37831543021160228836171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 201768229446187887126245 37831543021160228836171)
                    ·
                      rfl

theorem cell22_110515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 4].length) (baseStart_110515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110515 prefixEnd_110515 := by exact prefixLift 110515
  have htrace : WordTrace (prefixWord ++ tailWord_110515) baseStart_110515 baseEnd_110515 := by
    simpa [prefixWord, tailWord_110515, baseEnd_110515] using wordTrace_append hprefix tailTrace_110515
  have hstable : (prefixWord ++ tailWord_110515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110515).length < 2 ^ (prefixWord ++ tailWord_110515).sum := by decide
  have hdescent : baseEnd_110515 < baseStart_110515 := by decide
  rcases family_descends (prefixWord ++ tailWord_110515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110575 : List Nat := [1, 1, 2, 1, 4, 2, 3, 8]
def baseStart_110575 : Nat := 118140960795 + 110575 * 2 ^ 59
def prefixEnd_110575 : Nat := 4983230072969 + 3 ^ 40 * 110575 * 2
def baseEnd_110575 : Nat := 4205786916371119148443

theorem tailTrace_110575 : CollatzResearch.WordTrace tailWord_110575 prefixEnd_110575 4205786916371119148443 := by
  unfold tailWord_110575
  simp only [CollatzResearch.WordTrace]
  refine ⟨4033001574413134551621179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2688667716275423034414119 4033001574413134551621179)
  ·
    refine ⟨6049502361619701827431769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4033001574413134551621179 6049502361619701827431769)
    ·
      refine ⟨4537126771214776370573827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6049502361619701827431769 4537126771214776370573827)
      ·
        refine ⟨6805690156822164555860741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4537126771214776370573827 6805690156822164555860741)
        ·
          refine ⟨1276066904404155854223889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6805690156822164555860741 1276066904404155854223889)
          ·
            refine ⟨957050178303116890667917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1276066904404155854223889 957050178303116890667917)
            ·
              refine ⟨358893816863668834000469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 957050178303116890667917 358893816863668834000469)
              ·
                refine ⟨4205786916371119148443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 358893816863668834000469 4205786916371119148443)
                ·
                  rfl

theorem cell22_110575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 8].length) (baseStart_110575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110575 prefixEnd_110575 := by exact prefixLift 110575
  have htrace : WordTrace (prefixWord ++ tailWord_110575) baseStart_110575 baseEnd_110575 := by
    simpa [prefixWord, tailWord_110575, baseEnd_110575] using wordTrace_append hprefix tailTrace_110575
  have hstable : (prefixWord ++ tailWord_110575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110575).length < 2 ^ (prefixWord ++ tailWord_110575).sum := by decide
  have hdescent : baseEnd_110575 < baseStart_110575 := by decide
  rcases family_descends (prefixWord ++ tailWord_110575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110613 : List Nat := [1, 3, 2, 1, 5, 2, 2, 1, 2, 3]
def baseStart_110613 : Nat := 118140960795 + 110613 * 2 ^ 59
def prefixEnd_110613 : Nat := 4983230072969 + 3 ^ 40 * 110613 * 2
def baseEnd_110613 : Nat := 37865090423920639885871

theorem tailTrace_110613 : CollatzResearch.WordTrace tailWord_110613 prefixEnd_110613 37865090423920639885871 := by
  unfold tailWord_110613
  simp only [CollatzResearch.WordTrace]
  refine ⟨4034387548275467041504493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2689591698850311361002995 4034387548275467041504493)
  ·
    refine ⟨1512895330603300140564185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4034387548275467041504493 1512895330603300140564185)
    ·
      refine ⟨1134671497952475105423139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1512895330603300140564185 1134671497952475105423139)
      ·
        refine ⟨1702007246928712658134709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134671497952475105423139 1702007246928712658134709)
        ·
          refine ⟨159563179399566811700129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1702007246928712658134709 159563179399566811700129)
          ·
            refine ⟨119672384549675108775097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159563179399566811700129 119672384549675108775097)
            ·
              refine ⟨89754288412256331581323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119672384549675108775097 89754288412256331581323)
              ·
                refine ⟨134631432618384497371985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89754288412256331581323 134631432618384497371985)
                ·
                  refine ⟨100973574463788373028989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134631432618384497371985 100973574463788373028989)
                  ·
                    refine ⟨37865090423920639885871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100973574463788373028989 37865090423920639885871)
                    ·
                      rfl

theorem cell22_110613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_110613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110613 prefixEnd_110613 := by exact prefixLift 110613
  have htrace : WordTrace (prefixWord ++ tailWord_110613) baseStart_110613 baseEnd_110613 := by
    simpa [prefixWord, tailWord_110613, baseEnd_110613] using wordTrace_append hprefix tailTrace_110613
  have hstable : (prefixWord ++ tailWord_110613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110613).length < 2 ^ (prefixWord ++ tailWord_110613).sum := by decide
  have hdescent : baseEnd_110613 < baseStart_110613 := by decide
  rcases family_descends (prefixWord ++ tailWord_110613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110635 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 3, 7]
def baseStart_110635 : Nat := 118140960795 + 110635 * 2 ^ 59
def prefixEnd_110635 : Nat := 4983230072969 + 3 ^ 40 * 110635 * 2
def baseEnd_110635 : Nat := 37872621473519915835803

theorem tailTrace_110635 : CollatzResearch.WordTrace tailWord_110635 prefixEnd_110635 37872621473519915835803 := by
  unfold tailWord_110635
  simp only [CollatzResearch.WordTrace]
  refine ⟨4035189954195764798805359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2690126636130509865870239 4035189954195764798805359)
  ·
    refine ⟨6052784931293647198208039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4035189954195764798805359 6052784931293647198208039)
    ·
      refine ⟨9079177396940470797312059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6052784931293647198208039 9079177396940470797312059)
      ·
        refine ⟨13618766095410706195968089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9079177396940470797312059 13618766095410706195968089)
        ·
          refine ⟨10214074571558029646976067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13618766095410706195968089 10214074571558029646976067)
          ·
            refine ⟨15321111857337044470464101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10214074571558029646976067 15321111857337044470464101)
            ·
              refine ⟨2872708473250695838212019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15321111857337044470464101 2872708473250695838212019)
              ·
                refine ⟨4309062709876043757318029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2872708473250695838212019 4309062709876043757318029)
                ·
                  refine ⟨1615898516203516408994261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4309062709876043757318029 1615898516203516408994261)
                  ·
                    refine ⟨37872621473519915835803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1615898516203516408994261 37872621473519915835803)
                    ·
                      rfl

theorem cell22_110635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_110635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110635 prefixEnd_110635 := by exact prefixLift 110635
  have htrace : WordTrace (prefixWord ++ tailWord_110635) baseStart_110635 baseEnd_110635 := by
    simpa [prefixWord, tailWord_110635, baseEnd_110635] using wordTrace_append hprefix tailTrace_110635
  have hstable : (prefixWord ++ tailWord_110635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110635).length < 2 ^ (prefixWord ++ tailWord_110635).sum := by decide
  have hdescent : baseEnd_110635 < baseStart_110635 := by decide
  rcases family_descends (prefixWord ++ tailWord_110635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110652 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 2, 5]
def baseStart_110652 : Nat := 118140960795 + 110652 * 2 ^ 59
def prefixEnd_110652 : Nat := 4983230072969 + 3 ^ 40 * 110652 * 2
def baseEnd_110652 : Nat := 37878440920937538160751

theorem tailTrace_110652 : CollatzResearch.WordTrace tailWord_110652 prefixEnd_110652 37878440920937538160751 := by
  unfold tailWord_110652
  simp only [CollatzResearch.WordTrace]
  refine ⟨2017904997567088351087105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2690539996756117801449473 2017904997567088351087105)
  ·
    refine ⟨1513428748175316263315329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2017904997567088351087105 1513428748175316263315329)
    ·
      refine ⟨1135071561131487197486497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1513428748175316263315329 1135071561131487197486497)
      ·
        refine ⟨851303670848615398114873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1135071561131487197486497 851303670848615398114873)
        ·
          refine ⟨638477753136461548586155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 851303670848615398114873 638477753136461548586155)
          ·
            refine ⟨957716629704692322879233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638477753136461548586155 957716629704692322879233)
            ·
              refine ⟨718287472278519242159425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 957716629704692322879233 718287472278519242159425)
              ·
                refine ⟨538715604208889431619569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718287472278519242159425 538715604208889431619569)
                ·
                  refine ⟨404036703156667073714677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538715604208889431619569 404036703156667073714677)
                  ·
                    refine ⟨37878440920937538160751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 404036703156667073714677 37878440920937538160751)
                    ·
                      rfl

theorem cell22_110652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_110652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110652 prefixEnd_110652 := by exact prefixLift 110652
  have htrace : WordTrace (prefixWord ++ tailWord_110652) baseStart_110652 baseEnd_110652 := by
    simpa [prefixWord, tailWord_110652, baseEnd_110652] using wordTrace_append hprefix tailTrace_110652
  have hstable : (prefixWord ++ tailWord_110652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110652).length < 2 ^ (prefixWord ++ tailWord_110652).sum := by decide
  have hdescent : baseEnd_110652 < baseStart_110652 := by decide
  rcases family_descends (prefixWord ++ tailWord_110652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110669 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_110669 : Nat := 118140960795 + 110669 * 2 ^ 59
def prefixEnd_110669 : Nat := 4983230072969 + 3 ^ 40 * 110669 * 2
def baseEnd_110669 : Nat := 37884260368355160485699

theorem tailTrace_110669 : CollatzResearch.WordTrace tailWord_110669 prefixEnd_110669 37884260368355160485699 := by
  unfold tailWord_110669
  simp only [CollatzResearch.WordTrace]
  refine ⟨4036430036072588605543061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2690953357381725737028707 4036430036072588605543061)
  ·
    refine ⟨189207657940902590884831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4036430036072588605543061 189207657940902590884831)
    ·
      refine ⟨283811486911353886327247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189207657940902590884831 283811486911353886327247)
      ·
        refine ⟨425717230367030829490871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283811486911353886327247 425717230367030829490871)
        ·
          refine ⟨638575845550546244236307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425717230367030829490871 638575845550546244236307)
          ·
            refine ⟨957863768325819366354461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638575845550546244236307 957863768325819366354461)
            ·
              refine ⟨359198913122182262382923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 957863768325819366354461 359198913122182262382923)
              ·
                refine ⟨538798369683273393574385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359198913122182262382923 538798369683273393574385)
                ·
                  refine ⟨404098777262455045180789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 538798369683273393574385 404098777262455045180789)
                  ·
                    refine ⟨37884260368355160485699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 404098777262455045180789 37884260368355160485699)
                    ·
                      rfl

theorem cell22_110669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_110669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110669 prefixEnd_110669 := by exact prefixLift 110669
  have htrace : WordTrace (prefixWord ++ tailWord_110669) baseStart_110669 baseEnd_110669 := by
    simpa [prefixWord, tailWord_110669, baseEnd_110669] using wordTrace_append hprefix tailTrace_110669
  have hstable : (prefixWord ++ tailWord_110669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110669).length < 2 ^ (prefixWord ++ tailWord_110669).sum := by decide
  have hdescent : baseEnd_110669 < baseStart_110669 := by decide
  rcases family_descends (prefixWord ++ tailWord_110669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110682 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 6]
def baseStart_110682 : Nat := 118140960795 + 110682 * 2 ^ 59
def prefixEnd_110682 : Nat := 4983230072969 + 3 ^ 40 * 110682 * 2
def baseEnd_110682 : Nat := 12629570178009153303553

theorem tailTrace_110682 : CollatzResearch.WordTrace tailWord_110682 prefixEnd_110682 12629570178009153303553 := by
  unfold tailWord_110682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1009226046256372956441575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2691269456683661217177533 1009226046256372956441575)
  ·
    refine ⟨1513839069384559434662363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1009226046256372956441575 1513839069384559434662363)
    ·
      refine ⟨2270758604076839151993545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1513839069384559434662363 2270758604076839151993545)
      ·
        refine ⟨1703068953057629363995159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2270758604076839151993545 1703068953057629363995159)
        ·
          refine ⟨2554603429586444045992739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1703068953057629363995159 2554603429586444045992739)
          ·
            refine ⟨3831905144379666068989109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2554603429586444045992739 3831905144379666068989109)
            ·
              refine ⟨359241107285593693967729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3831905144379666068989109 359241107285593693967729)
              ·
                refine ⟨269430830464195270475797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359241107285593693967729 269430830464195270475797)
                ·
                  refine ⟨12629570178009153303553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 269430830464195270475797 12629570178009153303553)
                  ·
                    rfl

theorem cell22_110682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_110682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110682 prefixEnd_110682 := by exact prefixLift 110682
  have htrace : WordTrace (prefixWord ++ tailWord_110682) baseStart_110682 baseEnd_110682 := by
    simpa [prefixWord, tailWord_110682, baseEnd_110682] using wordTrace_append hprefix tailTrace_110682
  have hstable : (prefixWord ++ tailWord_110682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110682).length < 2 ^ (prefixWord ++ tailWord_110682).sum := by decide
  have hdescent : baseEnd_110682 < baseStart_110682 := by decide
  rcases family_descends (prefixWord ++ tailWord_110682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110684 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_110684 : Nat := 118140960795 + 110684 * 2 ^ 59
def prefixEnd_110684 : Nat := 4983230072969 + 3 ^ 40 * 110684 * 2
def baseEnd_110684 : Nat := 37889395174900121360653

theorem tailTrace_110684 : CollatzResearch.WordTrace tailWord_110684 prefixEnd_110684 37889395174900121360653 := by
  unfold tailWord_110684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2018488565509123083669553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2691318087345497444892737 2018488565509123083669553)
  ·
    refine ⟨1513866424131842312752165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2018488565509123083669553 1513866424131842312752165)
    ·
      refine ⟨283849954524720433641031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1513866424131842312752165 283849954524720433641031)
      ·
        refine ⟨425774931787080650461547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283849954524720433641031 425774931787080650461547)
        ·
          refine ⟨638662397680620975692321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425774931787080650461547 638662397680620975692321)
          ·
            refine ⟨478996798260465731769241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638662397680620975692321 478996798260465731769241)
            ·
              refine ⟨359247598695349298826931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478996798260465731769241 359247598695349298826931)
              ·
                refine ⟨538871398043023948240397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359247598695349298826931 538871398043023948240397)
                ·
                  refine ⟨202076774266133980590149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 538871398043023948240397 202076774266133980590149)
                  ·
                    refine ⟨37889395174900121360653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202076774266133980590149 37889395174900121360653)
                    ·
                      rfl

theorem cell22_110684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_110684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110684 prefixEnd_110684 := by exact prefixLift 110684
  have htrace : WordTrace (prefixWord ++ tailWord_110684) baseStart_110684 baseEnd_110684 := by
    simpa [prefixWord, tailWord_110684, baseEnd_110684] using wordTrace_append hprefix tailTrace_110684
  have hstable : (prefixWord ++ tailWord_110684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110684).length < 2 ^ (prefixWord ++ tailWord_110684).sum := by decide
  have hdescent : baseEnd_110684 < baseStart_110684 := by decide
  rcases family_descends (prefixWord ++ tailWord_110684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110697 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 1, 5]
def baseStart_110697 : Nat := 118140960795 + 110697 * 2 ^ 59
def prefixEnd_110697 : Nat := 4983230072969 + 3 ^ 40 * 110697 * 2
def baseEnd_110697 : Nat := 37893845340572420785613

theorem tailTrace_110697 : CollatzResearch.WordTrace tailWord_110697 prefixEnd_110697 37893845340572420785613 := by
  unfold tailWord_110697
  simp only [CollatzResearch.WordTrace]
  refine ⟨4037451279971149387562345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2691634186647432925041563 4037451279971149387562345)
  ·
    refine ⟨3028088459978362040671759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4037451279971149387562345 3028088459978362040671759)
    ·
      refine ⟨4542132689967543061007639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3028088459978362040671759 4542132689967543061007639)
      ·
        refine ⟨6813199034951314591511459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4542132689967543061007639 6813199034951314591511459)
        ·
          refine ⟨10219798552426971887267189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6813199034951314591511459 10219798552426971887267189)
          ·
            refine ⟨958106114290028614431299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10219798552426971887267189 958106114290028614431299)
            ·
              refine ⟨1437159171435042921646949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958106114290028614431299 1437159171435042921646949)
              ·
                refine ⟨269467344644070547808803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1437159171435042921646949 269467344644070547808803)
                ·
                  refine ⟨404201016966105821713205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 269467344644070547808803 404201016966105821713205)
                  ·
                    refine ⟨37893845340572420785613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 404201016966105821713205 37893845340572420785613)
                    ·
                      rfl

theorem cell22_110697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_110697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110697 prefixEnd_110697 := by exact prefixLift 110697
  have htrace : WordTrace (prefixWord ++ tailWord_110697) baseStart_110697 baseEnd_110697 := by
    simpa [prefixWord, tailWord_110697, baseEnd_110697] using wordTrace_append hprefix tailTrace_110697
  have hstable : (prefixWord ++ tailWord_110697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110697).length < 2 ^ (prefixWord ++ tailWord_110697).sum := by decide
  have hdescent : baseEnd_110697 < baseStart_110697 := by decide
  rcases family_descends (prefixWord ++ tailWord_110697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110712 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 4, 4]
def baseStart_110712 : Nat := 118140960795 + 110712 * 2 ^ 59
def prefixEnd_110712 : Nat := 4983230072969 + 3 ^ 40 * 110712 * 2
def baseEnd_110712 : Nat := 37898980147117381660567

theorem tailTrace_110712 : CollatzResearch.WordTrace tailWord_110712 prefixEnd_110712 37898980147117381660567 := by
  unfold tailWord_110712
  simp only [CollatzResearch.WordTrace]
  refine ⟨2018999187458403474679195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2691998916611204632905593 2018999187458403474679195)
  ·
    refine ⟨3028498781187605212018793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2018999187458403474679195 3028498781187605212018793)
    ·
      refine ⟨2271374085890703909014095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3028498781187605212018793 2271374085890703909014095)
      ·
        refine ⟨3407061128836055863521143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2271374085890703909014095 3407061128836055863521143)
        ·
          refine ⟨5110591693254083795281715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3407061128836055863521143 5110591693254083795281715)
          ·
            refine ⟨7665887539881125692922573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5110591693254083795281715 7665887539881125692922573)
            ·
              refine ⟨2874707827455422134845965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7665887539881125692922573 2874707827455422134845965)
              ·
                refine ⟨1078015435295783300567237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2874707827455422134845965 1078015435295783300567237)
                ·
                  refine ⟨202127894117959368856357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1078015435295783300567237 202127894117959368856357)
                  ·
                    refine ⟨37898980147117381660567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202127894117959368856357 37898980147117381660567)
                    ·
                      rfl

theorem cell22_110712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_110712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110712 prefixEnd_110712 := by exact prefixLift 110712
  have htrace : WordTrace (prefixWord ++ tailWord_110712) baseStart_110712 baseEnd_110712 := by
    simpa [prefixWord, tailWord_110712, baseEnd_110712] using wordTrace_append hprefix tailTrace_110712
  have hstable : (prefixWord ++ tailWord_110712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110712).length < 2 ^ (prefixWord ++ tailWord_110712).sum := by decide
  have hdescent : baseEnd_110712 < baseStart_110712 := by decide
  rcases family_descends (prefixWord ++ tailWord_110712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110744 : List Nat := [2, 1, 2, 4, 3, 1, 1, 8]
def baseStart_110744 : Nat := 118140960795 + 110744 * 2 ^ 59
def prefixEnd_110744 : Nat := 4983230072969 + 3 ^ 40 * 110744 * 2
def baseEnd_110744 : Nat := 4212214933453329428941

theorem tailTrace_110744 : CollatzResearch.WordTrace tailWord_110744 prefixEnd_110744 4212214933453329428941 := by
  unfold tailWord_110744
  simp only [CollatzResearch.WordTrace]
  refine ⟨2019582755400438207261643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2692777007200584276348857 2019582755400438207261643)
  ·
    refine ⟨3029374133100657310892465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2019582755400438207261643 3029374133100657310892465)
    ·
      refine ⟨2272030599825492983169349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3029374133100657310892465 2272030599825492983169349)
      ·
        refine ⟨426005737467279934344253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2272030599825492983169349 426005737467279934344253)
        ·
          refine ⟨159752151550229975379095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426005737467279934344253 159752151550229975379095)
          ·
            refine ⟨239628227325344963068643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159752151550229975379095 239628227325344963068643)
            ·
              refine ⟨359442340988017444602965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239628227325344963068643 359442340988017444602965)
              ·
                refine ⟨4212214933453329428941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 359442340988017444602965 4212214933453329428941)
                ·
                  rfl

theorem cell22_110744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 8].length) (baseStart_110744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110744 prefixEnd_110744 := by exact prefixLift 110744
  have htrace : WordTrace (prefixWord ++ tailWord_110744) baseStart_110744 baseEnd_110744 := by
    simpa [prefixWord, tailWord_110744, baseEnd_110744] using wordTrace_append hprefix tailTrace_110744
  have hstable : (prefixWord ++ tailWord_110744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110744).length < 2 ^ (prefixWord ++ tailWord_110744).sum := by decide
  have hdescent : baseEnd_110744 < baseStart_110744 := by decide
  rcases family_descends (prefixWord ++ tailWord_110744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110750 : List Nat := [4, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_110750 : Nat := 118140960795 + 110750 * 2 ^ 59
def prefixEnd_110750 : Nat := 4983230072969 + 3 ^ 40 * 110750 * 2
def baseEnd_110750 : Nat := 12637329441232649736817

theorem tailTrace_110750 : CollatzResearch.WordTrace tailWord_110750 prefixEnd_110750 12637329441232649736817 := by
  unfold tailWord_110750
  simp only [CollatzResearch.WordTrace]
  refine ⟨504923043597392429905213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2692922899186092959494469 504923043597392429905213)
  ·
    refine ⟨189346141349022161214455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 504923043597392429905213 189346141349022161214455)
    ·
      refine ⟨284019212023533241821683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189346141349022161214455 284019212023533241821683)
      ·
        refine ⟨426028818035299862732525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284019212023533241821683 426028818035299862732525)
        ·
          refine ⟨159760806763237448524697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426028818035299862732525 159760806763237448524697)
          ·
            refine ⟨119820605072428086393523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159760806763237448524697 119820605072428086393523)
            ·
              refine ⟨179730907608642129590285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119820605072428086393523 179730907608642129590285)
              ·
                refine ⟨67399090353240798596357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179730907608642129590285 67399090353240798596357)
                ·
                  refine ⟨12637329441232649736817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67399090353240798596357 12637329441232649736817)
                  ·
                    rfl

theorem cell22_110750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_110750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110750 prefixEnd_110750 := by exact prefixLift 110750
  have htrace : WordTrace (prefixWord ++ tailWord_110750) baseStart_110750 baseEnd_110750 := by
    simpa [prefixWord, tailWord_110750, baseEnd_110750] using wordTrace_append hprefix tailTrace_110750
  have hstable : (prefixWord ++ tailWord_110750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110750).length < 2 ^ (prefixWord ++ tailWord_110750).sum := by decide
  have hdescent : baseEnd_110750 < baseStart_110750 := by decide
  rcases family_descends (prefixWord ++ tailWord_110750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110782 : List Nat := [4, 2, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_110782 : Nat := 118140960795 + 110782 * 2 ^ 59
def prefixEnd_110782 : Nat := 4983230072969 + 3 ^ 40 * 110782 * 2
def baseEnd_110782 : Nat := 37922942577660532410353

theorem tailTrace_110782 : CollatzResearch.WordTrace tailWord_110782 prefixEnd_110782 37922942577660532410353 := by
  unfold tailWord_110782
  simp only [CollatzResearch.WordTrace]
  refine ⟨505068935582901113050825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2693700989775472602937733 505068935582901113050825)
  ·
    refine ⟨378801701687175834788119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 505068935582901113050825 378801701687175834788119)
    ·
      refine ⟨568202552530763752182179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378801701687175834788119 568202552530763752182179)
      ·
        refine ⟨852303828796145628273269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568202552530763752182179 852303828796145628273269)
        ·
          refine ⟨79903483949638652650619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 852303828796145628273269 79903483949638652650619)
          ·
            refine ⟨119855225924457978975929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79903483949638652650619 119855225924457978975929)
            ·
              refine ⟨89891419443343484231947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119855225924457978975929 89891419443343484231947)
              ·
                refine ⟨134837129165015226347921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89891419443343484231947 134837129165015226347921)
                ·
                  refine ⟨101127846873761419760941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134837129165015226347921 101127846873761419760941)
                  ·
                    refine ⟨37922942577660532410353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101127846873761419760941 37922942577660532410353)
                    ·
                      rfl

theorem cell22_110782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_110782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110782 prefixEnd_110782 := by exact prefixLift 110782
  have htrace : WordTrace (prefixWord ++ tailWord_110782) baseStart_110782 baseEnd_110782 := by
    simpa [prefixWord, tailWord_110782, baseEnd_110782] using wordTrace_append hprefix tailTrace_110782
  have hstable : (prefixWord ++ tailWord_110782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110782).length < 2 ^ (prefixWord ++ tailWord_110782).sum := by decide
  have hdescent : baseEnd_110782 < baseStart_110782 := by decide
  rcases family_descends (prefixWord ++ tailWord_110782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110787 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 6, 5]
def baseStart_110787 : Nat := 118140960795 + 110787 * 2 ^ 59
def prefixEnd_110787 : Nat := 4983230072969 + 3 ^ 40 * 110787 * 2
def baseEnd_110787 : Nat := 37924654179842186035337

theorem tailTrace_110787 : CollatzResearch.WordTrace tailWord_110787 prefixEnd_110787 37924654179842186035337 := by
  unfold tailWord_110787
  simp only [CollatzResearch.WordTrace]
  refine ⟨4040733849645094758338615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2693822566430063172225743 4040733849645094758338615)
  ·
    refine ⟨6061100774467642137507923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4040733849645094758338615 6061100774467642137507923)
    ·
      refine ⟨9091651161701463206261885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6061100774467642137507923 9091651161701463206261885)
      ·
        refine ⟨3409369185638048702348207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9091651161701463206261885 3409369185638048702348207)
        ·
          refine ⟨5114053778457073053522311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3409369185638048702348207 5114053778457073053522311)
          ·
            refine ⟨7671080667685609580283467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5114053778457073053522311 7671080667685609580283467)
            ·
              refine ⟨11506621001528414370425201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7671080667685609580283467 11506621001528414370425201)
              ·
                refine ⟨8629965751146310777818901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11506621001528414370425201 8629965751146310777818901)
                ·
                  refine ⟨404529644584983317710261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8629965751146310777818901 404529644584983317710261)
                  ·
                    refine ⟨37924654179842186035337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 404529644584983317710261 37924654179842186035337)
                    ·
                      rfl

theorem cell22_110787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 5].length) (baseStart_110787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110787 prefixEnd_110787 := by exact prefixLift 110787
  have htrace : WordTrace (prefixWord ++ tailWord_110787) baseStart_110787 baseEnd_110787 := by
    simpa [prefixWord, tailWord_110787, baseEnd_110787] using wordTrace_append hprefix tailTrace_110787
  have hstable : (prefixWord ++ tailWord_110787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110787).length < 2 ^ (prefixWord ++ tailWord_110787).sum := by decide
  have hdescent : baseEnd_110787 < baseStart_110787 := by decide
  rcases family_descends (prefixWord ++ tailWord_110787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110879 : List Nat := [1, 1, 2, 4, 3, 2, 9]
def baseStart_110879 : Nat := 118140960795 + 110879 * 2 ^ 59
def prefixEnd_110879 : Nat := 4983230072969 + 3 ^ 40 * 110879 * 2
def baseEnd_110879 : Nat := 1405783246666096767965

theorem tailTrace_110879 : CollatzResearch.WordTrace tailWord_110879 prefixEnd_110879 1405783246666096767965 := by
  unfold tailWord_110879
  simp only [CollatzResearch.WordTrace]
  refine ⟨4044089365311794470687691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2696059576874529647125127 4044089365311794470687691)
  ·
    refine ⟨6066134047967691706031537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4044089365311794470687691 6066134047967691706031537)
    ·
      refine ⟨4549600535975768779523653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6066134047967691706031537 4549600535975768779523653)
      ·
        refine ⟨853050100495456646160685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4549600535975768779523653 853050100495456646160685)
        ·
          refine ⟨319893787685796242310257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 853050100495456646160685 319893787685796242310257)
          ·
            refine ⟨239920340764347181732693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319893787685796242310257 239920340764347181732693)
            ·
              refine ⟨1405783246666096767965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 239920340764347181732693 1405783246666096767965)
              ·
                rfl

theorem cell22_110879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 9].length) (baseStart_110879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110879 prefixEnd_110879 := by exact prefixLift 110879
  have htrace : WordTrace (prefixWord ++ tailWord_110879) baseStart_110879 baseEnd_110879 := by
    simpa [prefixWord, tailWord_110879, baseEnd_110879] using wordTrace_append hprefix tailTrace_110879
  have hstable : (prefixWord ++ tailWord_110879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110879).length < 2 ^ (prefixWord ++ tailWord_110879).sum := by decide
  have hdescent : baseEnd_110879 < baseStart_110879 := by decide
  rcases family_descends (prefixWord ++ tailWord_110879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110911 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 3, 3]
def baseStart_110911 : Nat := 118140960795 + 110911 * 2 ^ 59
def prefixEnd_110911 : Nat := 4983230072969 + 3 ^ 40 * 110911 * 2
def baseEnd_110911 : Nat := 37967101913947195934957

theorem tailTrace_110911 : CollatzResearch.WordTrace tailWord_110911 prefixEnd_110911 37967101913947195934957 := by
  unfold tailWord_110911
  simp only [CollatzResearch.WordTrace]
  refine ⟨4045256501195863935852587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2696837667463909290568391 4045256501195863935852587)
  ·
    refine ⟨6067884751793795903778881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4045256501195863935852587 6067884751793795903778881)
    ·
      refine ⟨4550913563845346927834161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6067884751793795903778881 4550913563845346927834161)
      ·
        refine ⟨3413185172884010195875621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4550913563845346927834161 3413185172884010195875621)
        ·
          refine ⟨639972219915751911726679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3413185172884010195875621 639972219915751911726679)
          ·
            refine ⟨959958329873627867590019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639972219915751911726679 959958329873627867590019)
            ·
              refine ⟨1439937494810441801385029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959958329873627867590019 1439937494810441801385029)
              ·
                refine ⟨269988280276957837759693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1439937494810441801385029 269988280276957837759693)
                ·
                  refine ⟨101245605103859189159885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269988280276957837759693 101245605103859189159885)
                  ·
                    refine ⟨37967101913947195934957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101245605103859189159885 37967101913947195934957)
                    ·
                      rfl

theorem cell22_110911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 3, 3].length) (baseStart_110911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110911 prefixEnd_110911 := by exact prefixLift 110911
  have htrace : WordTrace (prefixWord ++ tailWord_110911) baseStart_110911 baseEnd_110911 := by
    simpa [prefixWord, tailWord_110911, baseEnd_110911] using wordTrace_append hprefix tailTrace_110911
  have hstable : (prefixWord ++ tailWord_110911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110911).length < 2 ^ (prefixWord ++ tailWord_110911).sum := by decide
  have hdescent : baseEnd_110911 < baseStart_110911 := by decide
  rcases family_descends (prefixWord ++ tailWord_110911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110924 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 9]
def baseStart_110924 : Nat := 118140960795 + 110924 * 2 ^ 59
def prefixEnd_110924 : Nat := 4983230072969 + 3 ^ 40 * 110924 * 2
def baseEnd_110924 : Nat := 12657184026539831786639

theorem tailTrace_110924 : CollatzResearch.WordTrace tailWord_110924 prefixEnd_110924 12657184026539831786639 := by
  unfold tailWord_110924
  simp only [CollatzResearch.WordTrace]
  refine ⟨2022865325074383578037913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2697153766765844770717217 2022865325074383578037913)
  ·
    refine ⟨1517148993805787683528435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2022865325074383578037913 1517148993805787683528435)
    ·
      refine ⟨2275723490708681525292653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1517148993805787683528435 2275723490708681525292653)
      ·
        refine ⟨853396309015755571984745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2275723490708681525292653 853396309015755571984745)
        ·
          refine ⟨640047231761816678988559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853396309015755571984745 640047231761816678988559)
          ·
            refine ⟨960070847642725018482839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640047231761816678988559 960070847642725018482839)
            ·
              refine ⟨1440106271464087527724259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960070847642725018482839 1440106271464087527724259)
              ·
                refine ⟨2160159407196131291586389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1440106271464087527724259 2160159407196131291586389)
                ·
                  refine ⟨12657184026539831786639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2160159407196131291586389 12657184026539831786639)
                  ·
                    rfl

theorem cell22_110924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_110924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110924 prefixEnd_110924 := by exact prefixLift 110924
  have htrace : WordTrace (prefixWord ++ tailWord_110924) baseStart_110924 baseEnd_110924 := by
    simpa [prefixWord, tailWord_110924, baseEnd_110924] using wordTrace_append hprefix tailTrace_110924
  have hstable : (prefixWord ++ tailWord_110924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110924).length < 2 ^ (prefixWord ++ tailWord_110924).sum := by decide
  have hdescent : baseEnd_110924 < baseStart_110924 := by decide
  rcases family_descends (prefixWord ++ tailWord_110924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110969 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 8]
def baseStart_110969 : Nat := 118140960795 + 110969 * 2 ^ 59
def prefixEnd_110969 : Nat := 4983230072969 + 3 ^ 40 * 110969 * 2
def baseEnd_110969 : Nat := 12662318833084792661593

theorem tailTrace_110969 : CollatzResearch.WordTrace tailWord_110969 prefixEnd_110969 12662318833084792661593 := by
  unfold tailWord_110969
  simp only [CollatzResearch.WordTrace]
  refine ⟨4047371934985739841463961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2698247956657159894309307 4047371934985739841463961)
  ·
    refine ⟨3035528951239304881097971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4047371934985739841463961 3035528951239304881097971)
    ·
      refine ⟨4553293426858957321646957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3035528951239304881097971 4553293426858957321646957)
      ·
        refine ⟨1707485035072108995617609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4553293426858957321646957 1707485035072108995617609)
        ·
          refine ⟨1280613776304081746713207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1707485035072108995617609 1280613776304081746713207)
          ·
            refine ⟨1920920664456122620069811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280613776304081746713207 1920920664456122620069811)
            ·
              refine ⟨2881380996684183930104717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1920920664456122620069811 2881380996684183930104717)
              ·
                refine ⟨1080517873756568973789269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2881380996684183930104717 1080517873756568973789269)
                ·
                  refine ⟨12662318833084792661593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1080517873756568973789269 12662318833084792661593)
                  ·
                    rfl

theorem cell22_110969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_110969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110969 prefixEnd_110969 := by exact prefixLift 110969
  have htrace : WordTrace (prefixWord ++ tailWord_110969) baseStart_110969 baseEnd_110969 := by
    simpa [prefixWord, tailWord_110969, baseEnd_110969] using wordTrace_append hprefix tailTrace_110969
  have hstable : (prefixWord ++ tailWord_110969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110969).length < 2 ^ (prefixWord ++ tailWord_110969).sum := by decide
  have hdescent : baseEnd_110969 < baseStart_110969 := by decide
  rcases family_descends (prefixWord ++ tailWord_110969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110971 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 3, 4]
def baseStart_110971 : Nat := 118140960795 + 110971 * 2 ^ 59
def prefixEnd_110971 : Nat := 4983230072969 + 3 ^ 40 * 110971 * 2
def baseEnd_110971 : Nat := 37987641140127039434773

theorem tailTrace_110971 : CollatzResearch.WordTrace tailWord_110971 prefixEnd_110971 37987641140127039434773 := by
  unfold tailWord_110971
  simp only [CollatzResearch.WordTrace]
  refine ⟨4047444880978494183036767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2698296587318996122024511 4047444880978494183036767)
  ·
    refine ⟨6071167321467741274555151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4047444880978494183036767 6071167321467741274555151)
    ·
      refine ⟨9106750982201611911832727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6071167321467741274555151 9106750982201611911832727)
      ·
        refine ⟨13660126473302417867749091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9106750982201611911832727 13660126473302417867749091)
        ·
          refine ⟨20490189709953626801623637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13660126473302417867749091 20490189709953626801623637)
          ·
            refine ⟨240119410663519064081527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 20490189709953626801623637 240119410663519064081527)
            ·
              refine ⟨360179115995278596122291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240119410663519064081527 360179115995278596122291)
              ·
                refine ⟨540268673992917894183437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360179115995278596122291 540268673992917894183437)
                ·
                  refine ⟨202600752747344210318789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 540268673992917894183437 202600752747344210318789)
                  ·
                    refine ⟨37987641140127039434773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202600752747344210318789 37987641140127039434773)
                    ·
                      rfl

theorem cell22_110971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 4].length) (baseStart_110971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110971 prefixEnd_110971 := by exact prefixLift 110971
  have htrace : WordTrace (prefixWord ++ tailWord_110971) baseStart_110971 baseEnd_110971 := by
    simpa [prefixWord, tailWord_110971, baseEnd_110971] using wordTrace_append hprefix tailTrace_110971
  have hstable : (prefixWord ++ tailWord_110971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110971).length < 2 ^ (prefixWord ++ tailWord_110971).sum := by decide
  have hdescent : baseEnd_110971 < baseStart_110971 := by decide
  rcases family_descends (prefixWord ++ tailWord_110971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110996 : List Nat := [2, 4, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_110996 : Nat := 118140960795 + 110996 * 2 ^ 59
def prefixEnd_110996 : Nat := 4983230072969 + 3 ^ 40 * 110996 * 2
def baseEnd_110996 : Nat := 37996199151035307559697

theorem tailTrace_110996 : CollatzResearch.WordTrace tailWord_110996 prefixEnd_110996 37996199151035307559697 := by
  unfold tailWord_110996
  simp only [CollatzResearch.WordTrace]
  refine ⟨2024178352943961726348421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2698904470591948968464561 2024178352943961726348421)
  ·
    refine ⟨379533441176992823690329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2024178352943961726348421 379533441176992823690329)
    ·
      refine ⟨284650080882744617767747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379533441176992823690329 284650080882744617767747)
      ·
        refine ⟨426975121324116926651621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284650080882744617767747 426975121324116926651621)
        ·
          refine ⟨80057835248271923747179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 426975121324116926651621 80057835248271923747179)
          ·
            refine ⟨120086752872407885620769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80057835248271923747179 120086752872407885620769)
            ·
              refine ⟨90065064654305914215577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120086752872407885620769 90065064654305914215577)
              ·
                refine ⟨67548798490729435661683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90065064654305914215577 67548798490729435661683)
                ·
                  refine ⟨101323197736094153492525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67548798490729435661683 101323197736094153492525)
                  ·
                    refine ⟨37996199151035307559697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101323197736094153492525 37996199151035307559697)
                    ·
                      rfl

theorem cell22_110996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_110996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_110996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_110996 prefixEnd_110996 := by exact prefixLift 110996
  have htrace : WordTrace (prefixWord ++ tailWord_110996) baseStart_110996 baseEnd_110996 := by
    simpa [prefixWord, tailWord_110996, baseEnd_110996] using wordTrace_append hprefix tailTrace_110996
  have hstable : (prefixWord ++ tailWord_110996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110996).length < 2 ^ (prefixWord ++ tailWord_110996).sum := by decide
  have hdescent : baseEnd_110996 < baseStart_110996 := by decide
  rcases family_descends (prefixWord ++ tailWord_110996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111033 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 2, 4]
def baseStart_111033 : Nat := 118140960795 + 111033 * 2 ^ 59
def prefixEnd_111033 : Nat := 4983230072969 + 3 ^ 40 * 111033 * 2
def baseEnd_111033 : Nat := 38008865007179544384583

theorem tailTrace_111033 : CollatzResearch.WordTrace tailWord_111033 prefixEnd_111033 38008865007179544384583 := by
  unfold tailWord_111033
  simp only [CollatzResearch.WordTrace]
  refine ⟨4049706206753878771793753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2699804137835919181195835 4049706206753878771793753)
  ·
    refine ⟨3037279655065409078845315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4049706206753878771793753 3037279655065409078845315)
    ·
      refine ⟨4555919482598113618267973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3037279655065409078845315 4555919482598113618267973)
      ·
        refine ⟨854234902987146303425245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4555919482598113618267973 854234902987146303425245)
        ·
          refine ⟨320338088620179863784467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 854234902987146303425245 320338088620179863784467)
          ·
            refine ⟨480507132930269795676701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320338088620179863784467 480507132930269795676701)
            ·
              refine ⟨180190174848851173378763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 480507132930269795676701 180190174848851173378763)
              ·
                refine ⟨270285262273276760068145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180190174848851173378763 270285262273276760068145)
                ·
                  refine ⟨202713946704957570051109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270285262273276760068145 202713946704957570051109)
                  ·
                    refine ⟨38008865007179544384583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202713946704957570051109 38008865007179544384583)
                    ·
                      rfl

theorem cell22_111033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_111033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111033 prefixEnd_111033 := by exact prefixLift 111033
  have htrace : WordTrace (prefixWord ++ tailWord_111033) baseStart_111033 baseEnd_111033 := by
    simpa [prefixWord, tailWord_111033, baseEnd_111033] using wordTrace_append hprefix tailTrace_111033
  have hstable : (prefixWord ++ tailWord_111033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111033).length < 2 ^ (prefixWord ++ tailWord_111033).sum := by decide
  have hdescent : baseEnd_111033 < baseStart_111033 := by decide
  rcases family_descends (prefixWord ++ tailWord_111033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111052 : List Nat := [2, 2, 1, 4, 3, 2, 1, 2, 2, 3]
def baseStart_111052 : Nat := 118140960795 + 111052 * 2 ^ 59
def prefixEnd_111052 : Nat := 4983230072969 + 3 ^ 40 * 111052 * 2
def baseEnd_111052 : Nat := 38015369095469828159525

theorem tailTrace_111052 : CollatzResearch.WordTrace tailWord_111052 prefixEnd_111052 38015369095469828159525 := by
  unfold tailWord_111052
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025199596842522508367705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2700266129123363344490273 2025199596842522508367705)
  ·
    refine ⟨1518899697631891881275779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2025199596842522508367705 1518899697631891881275779)
    ·
      refine ⟨2278349546447837821913669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1518899697631891881275779 2278349546447837821913669)
      ·
        refine ⟨427190539958969591608813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2278349546447837821913669 427190539958969591608813)
        ·
          refine ⟨160196452484613596853305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427190539958969591608813 160196452484613596853305)
          ·
            refine ⟨120147339363460197639979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160196452484613596853305 120147339363460197639979)
            ·
              refine ⟨180221009045190296459969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120147339363460197639979 180221009045190296459969)
              ·
                refine ⟨135165756783892722344977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180221009045190296459969 135165756783892722344977)
                ·
                  refine ⟨101374317587919541758733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135165756783892722344977 101374317587919541758733)
                  ·
                    refine ⟨38015369095469828159525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101374317587919541758733 38015369095469828159525)
                    ·
                      rfl

theorem cell22_111052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_111052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111052 prefixEnd_111052 := by exact prefixLift 111052
  have htrace : WordTrace (prefixWord ++ tailWord_111052) baseStart_111052 baseEnd_111052 := by
    simpa [prefixWord, tailWord_111052, baseEnd_111052] using wordTrace_append hprefix tailTrace_111052
  have hstable : (prefixWord ++ tailWord_111052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111052).length < 2 ^ (prefixWord ++ tailWord_111052).sum := by decide
  have hdescent : baseEnd_111052 < baseStart_111052 := by decide
  rcases family_descends (prefixWord ++ tailWord_111052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111121 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 6]
def baseStart_111121 : Nat := 118140960795 + 111121 * 2 ^ 59
def prefixEnd_111121 : Nat := 4983230072969 + 3 ^ 40 * 111121 * 2
def baseEnd_111121 : Nat := 12679663068525549394771

theorem tailTrace_111121 : CollatzResearch.WordTrace tailWord_111121 prefixEnd_111121 12679663068525549394771 := by
  unfold tailWord_111121
  simp only [CollatzResearch.WordTrace]
  refine ⟨4052915830435069800997217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2701943886956713200664811 4052915830435069800997217)
  ·
    refine ⟨3039686872826302350747913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4052915830435069800997217 3039686872826302350747913)
    ·
      refine ⟨2279765154619726763060935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3039686872826302350747913 2279765154619726763060935)
      ·
        refine ⟨3419647731929590144591403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2279765154619726763060935 3419647731929590144591403)
        ·
          refine ⟨5129471597894385216887105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3419647731929590144591403 5129471597894385216887105)
          ·
            refine ⟨3847103698420788912665329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5129471597894385216887105 3847103698420788912665329)
            ·
              refine ⟨2885327773815591684498997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3847103698420788912665329 2885327773815591684498997)
              ·
                refine ⟨270499478795211720421781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2885327773815591684498997 270499478795211720421781)
                ·
                  refine ⟨12679663068525549394771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 270499478795211720421781 12679663068525549394771)
                  ·
                    rfl

theorem cell22_111121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_111121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111121 prefixEnd_111121 := by exact prefixLift 111121
  have htrace : WordTrace (prefixWord ++ tailWord_111121) baseStart_111121 baseEnd_111121 := by
    simpa [prefixWord, tailWord_111121, baseEnd_111121] using wordTrace_append hprefix tailTrace_111121
  have hstable : (prefixWord ++ tailWord_111121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111121).length < 2 ^ (prefixWord ++ tailWord_111121).sum := by decide
  have hdescent : baseEnd_111121 < baseStart_111121 := by decide
  rcases family_descends (prefixWord ++ tailWord_111121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111153 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 6, 3]
def baseStart_111153 : Nat := 118140960795 + 111153 * 2 ^ 59
def prefixEnd_111153 : Nat := 4983230072969 + 3 ^ 40 * 111153 * 2
def baseEnd_111153 : Nat := 38049943459539231384215

theorem tailTrace_111153 : CollatzResearch.WordTrace tailWord_111153 prefixEnd_111153 38049943459539231384215 := by
  unfold tailWord_111153
  simp only [CollatzResearch.WordTrace]
  refine ⟨4054082966319139266162113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2702721977546092844108075 4054082966319139266162113)
  ·
    refine ⟨3040562224739354449621585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4054082966319139266162113 3040562224739354449621585)
    ·
      refine ⟨2280421668554515837216189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3040562224739354449621585 2280421668554515837216189)
      ·
        refine ⟨855158125707943438956071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2280421668554515837216189 855158125707943438956071)
        ·
          refine ⟨1282737188561915158434107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855158125707943438956071 1282737188561915158434107)
          ·
            refine ⟨1924105782842872737651161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1282737188561915158434107 1924105782842872737651161)
            ·
              refine ⟨1443079337132154553238371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1924105782842872737651161 1443079337132154553238371)
              ·
                refine ⟨2164619005698231829857557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1443079337132154553238371 2164619005698231829857557)
                ·
                  refine ⟨101466515892104617024573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2164619005698231829857557 101466515892104617024573)
                  ·
                    refine ⟨38049943459539231384215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101466515892104617024573 38049943459539231384215)
                    ·
                      rfl

theorem cell22_111153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_111153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111153 prefixEnd_111153 := by exact prefixLift 111153
  have htrace : WordTrace (prefixWord ++ tailWord_111153) baseStart_111153 baseEnd_111153 := by
    simpa [prefixWord, tailWord_111153, baseEnd_111153] using wordTrace_append hprefix tailTrace_111153
  have hstable : (prefixWord ++ tailWord_111153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111153).length < 2 ^ (prefixWord ++ tailWord_111153).sum := by decide
  have hdescent : baseEnd_111153 < baseStart_111153 := by decide
  rcases family_descends (prefixWord ++ tailWord_111153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111168 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 2, 4]
def baseStart_111168 : Nat := 118140960795 + 111168 * 2 ^ 59
def prefixEnd_111168 : Nat := 4983230072969 + 3 ^ 40 * 111168 * 2
def baseEnd_111168 : Nat := 38055078266084192259169

theorem tailTrace_111168 : CollatzResearch.WordTrace tailWord_111168 prefixEnd_111168 38055078266084192259169 := by
  unfold tailWord_111168
  simp only [CollatzResearch.WordTrace]
  refine ⟨2027315030632398413979079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2703086707509864551972105 2027315030632398413979079)
  ·
    refine ⟨3040972545948597620968619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2027315030632398413979079 3040972545948597620968619)
    ·
      refine ⟨4561458818922896431452929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3040972545948597620968619 4561458818922896431452929)
      ·
        refine ⟨3421094114192172323589697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4561458818922896431452929 3421094114192172323589697)
        ·
          refine ⟨2565820585644129242692273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3421094114192172323589697 2565820585644129242692273)
          ·
            refine ⟨1924365439233096932019205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2565820585644129242692273 1924365439233096932019205)
            ·
              refine ⟨360818519856205674753601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1924365439233096932019205 360818519856205674753601)
              ·
                refine ⟨270613889892154256065201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360818519856205674753601 270613889892154256065201)
                ·
                  refine ⟨202960417419115692048901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270613889892154256065201 202960417419115692048901)
                  ·
                    refine ⟨38055078266084192259169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202960417419115692048901 38055078266084192259169)
                    ·
                      rfl

theorem cell22_111168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2, 4].length) (baseStart_111168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111168 prefixEnd_111168 := by exact prefixLift 111168
  have htrace : WordTrace (prefixWord ++ tailWord_111168) baseStart_111168 baseEnd_111168 := by
    simpa [prefixWord, tailWord_111168, baseEnd_111168] using wordTrace_append hprefix tailTrace_111168
  have hstable : (prefixWord ++ tailWord_111168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111168).length < 2 ^ (prefixWord ++ tailWord_111168).sum := by decide
  have hdescent : baseEnd_111168 < baseStart_111168 := by decide
  rcases family_descends (prefixWord ++ tailWord_111168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111202 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_111202 : Nat := 118140960795 + 111202 * 2 ^ 59
def prefixEnd_111202 : Nat := 4983230072969 + 3 ^ 40 * 111202 * 2
def baseEnd_111202 : Nat := 38066717160919436909065

theorem tailTrace_111202 : CollatzResearch.WordTrace tailWord_111202 prefixEnd_111202 38066717160919436909065 := by
  unfold tailWord_111202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013967535785405158673965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2703913428761080423130573 1013967535785405158673965)
  ·
    refine ⟨380237825919526934502737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1013967535785405158673965 380237825919526934502737)
    ·
      refine ⟨285178369439645200877053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380237825919526934502737 285178369439645200877053)
      ·
        refine ⟨106941888539866950328895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285178369439645200877053 106941888539866950328895)
        ·
          refine ⟨160412832809800425493343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106941888539866950328895 160412832809800425493343)
          ·
            refine ⟨240619249214700638240015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160412832809800425493343 240619249214700638240015)
            ·
              refine ⟨360928873822050957360023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240619249214700638240015 360928873822050957360023)
              ·
                refine ⟨541393310733076436040035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360928873822050957360023 541393310733076436040035)
                ·
                  refine ⟨812089966099614654060053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541393310733076436040035 812089966099614654060053)
                  ·
                    refine ⟨38066717160919436909065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 812089966099614654060053 38066717160919436909065)
                    ·
                      rfl

theorem cell22_111202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_111202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111202 prefixEnd_111202 := by exact prefixLift 111202
  have htrace : WordTrace (prefixWord ++ tailWord_111202) baseStart_111202 baseEnd_111202 := by
    simpa [prefixWord, tailWord_111202, baseEnd_111202] using wordTrace_append hprefix tailTrace_111202
  have hstable : (prefixWord ++ tailWord_111202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111202).length < 2 ^ (prefixWord ++ tailWord_111202).sum := by decide
  have hdescent : baseEnd_111202 < baseStart_111202 := by decide
  rcases family_descends (prefixWord ++ tailWord_111202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111221 : List Nat := [1, 3, 4, 2, 3, 1, 1, 2, 2, 3]
def baseStart_111221 : Nat := 118140960795 + 111221 * 2 ^ 59
def prefixEnd_111221 : Nat := 4983230072969 + 3 ^ 40 * 111221 * 2
def baseEnd_111221 : Nat := 38073221249209720684007

theorem tailTrace_111221 : CollatzResearch.WordTrace tailWord_111221 prefixEnd_111221 38073221249209720684007 := by
  unfold tailWord_111221
  simp only [CollatzResearch.WordTrace]
  refine ⟨4056563130072786879637517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2704375420048524586425011 4056563130072786879637517)
  ·
    refine ⟨1521211173777295079864069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4056563130072786879637517 1521211173777295079864069)
    ·
      refine ⟨285227095083242827474513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1521211173777295079864069 285227095083242827474513)
      ·
        refine ⟨213920321312432120605885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285227095083242827474513 213920321312432120605885)
        ·
          refine ⟨80220120492162045227207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213920321312432120605885 80220120492162045227207)
          ·
            refine ⟨120330180738243067840811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80220120492162045227207 120330180738243067840811)
            ·
              refine ⟨180495271107364601761217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120330180738243067840811 180495271107364601761217)
              ·
                refine ⟨135371453330523451320913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180495271107364601761217 135371453330523451320913)
                ·
                  refine ⟨101528589997892588490685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135371453330523451320913 101528589997892588490685)
                  ·
                    refine ⟨38073221249209720684007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101528589997892588490685 38073221249209720684007)
                    ·
                      rfl

theorem cell22_111221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_111221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111221 prefixEnd_111221 := by exact prefixLift 111221
  have htrace : WordTrace (prefixWord ++ tailWord_111221) baseStart_111221 baseEnd_111221 := by
    simpa [prefixWord, tailWord_111221, baseEnd_111221] using wordTrace_append hprefix tailTrace_111221
  have hstable : (prefixWord ++ tailWord_111221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111221).length < 2 ^ (prefixWord ++ tailWord_111221).sum := by decide
  have hdescent : baseEnd_111221 < baseStart_111221 := by decide
  rcases family_descends (prefixWord ++ tailWord_111221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111232 : List Nat := [2, 1, 1, 2, 1, 5, 2, 4, 1, 3]
def baseStart_111232 : Nat := 118140960795 + 111232 * 2 ^ 59
def prefixEnd_111232 : Nat := 4983230072969 + 3 ^ 40 * 111232 * 2
def baseEnd_111232 : Nat := 38076986774009358658973

theorem tailTrace_111232 : CollatzResearch.WordTrace tailWord_111232 prefixEnd_111232 38076986774009358658973 := by
  unfold tailWord_111232
  simp only [CollatzResearch.WordTrace]
  refine ⟨2028482166516467879143975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2704642888688623838858633 2028482166516467879143975)
  ·
    refine ⟨3042723249774701818715963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2028482166516467879143975 3042723249774701818715963)
    ·
      refine ⟨4564084874662052728073945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3042723249774701818715963 4564084874662052728073945)
      ·
        refine ⟨3423063655996539546055459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4564084874662052728073945 3423063655996539546055459)
        ·
          refine ⟨5134595483994809319083189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423063655996539546055459 5134595483994809319083189)
          ·
            refine ⟨481368326624513373664049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5134595483994809319083189 481368326624513373664049)
            ·
              refine ⟨361026244968385030248037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481368326624513373664049 361026244968385030248037)
              ·
                refine ⟨67692420931572193171507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 361026244968385030248037 67692420931572193171507)
                ·
                  refine ⟨101538631397358289757261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67692420931572193171507 101538631397358289757261)
                  ·
                    refine ⟨38076986774009358658973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101538631397358289757261 38076986774009358658973)
                    ·
                      rfl

theorem cell22_111232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 1, 3].length) (baseStart_111232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111232 prefixEnd_111232 := by exact prefixLift 111232
  have htrace : WordTrace (prefixWord ++ tailWord_111232) baseStart_111232 baseEnd_111232 := by
    simpa [prefixWord, tailWord_111232, baseEnd_111232] using wordTrace_append hprefix tailTrace_111232
  have hstable : (prefixWord ++ tailWord_111232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111232).length < 2 ^ (prefixWord ++ tailWord_111232).sum := by decide
  have hdescent : baseEnd_111232 < baseStart_111232 := by decide
  rcases family_descends (prefixWord ++ tailWord_111232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111303 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 1, 6]
def baseStart_111303 : Nat := 118140960795 + 111303 * 2 ^ 59
def prefixEnd_111303 : Nat := 4983230072969 + 3 ^ 40 * 111303 * 2
def baseEnd_111303 : Nat := 38101291524988840133755

theorem tailTrace_111303 : CollatzResearch.WordTrace tailWord_111303 prefixEnd_111303 38101291524988840133755 := by
  unfold tailWord_111303
  simp only [CollatzResearch.WordTrace]
  refine ⟨4059553915775714884122563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2706369277183809922748375 4059553915775714884122563)
  ·
    refine ⟨6089330873663572326183845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4059553915775714884122563 6089330873663572326183845)
    ·
      refine ⟨1141749538811919811159471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6089330873663572326183845 1141749538811919811159471)
      ·
        refine ⟨1712624308217879716739207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1141749538811919811159471 1712624308217879716739207)
        ·
          refine ⟨2568936462326819575108811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1712624308217879716739207 2568936462326819575108811)
          ·
            refine ⟨3853404693490229362663217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2568936462326819575108811 3853404693490229362663217)
            ·
              refine ⟨2890053520117672021997413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3853404693490229362663217 2890053520117672021997413)
              ·
                refine ⟨541885035022063504124515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2890053520117672021997413 541885035022063504124515)
                ·
                  refine ⟨812827552533095256186773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 541885035022063504124515 812827552533095256186773)
                  ·
                    refine ⟨38101291524988840133755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 812827552533095256186773 38101291524988840133755)
                    ·
                      rfl

theorem cell22_111303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_111303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111303 prefixEnd_111303 := by exact prefixLift 111303
  have htrace : WordTrace (prefixWord ++ tailWord_111303) baseStart_111303 baseEnd_111303 := by
    simpa [prefixWord, tailWord_111303, baseEnd_111303] using wordTrace_append hprefix tailTrace_111303
  have hstable : (prefixWord ++ tailWord_111303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111303).length < 2 ^ (prefixWord ++ tailWord_111303).sum := by decide
  have hdescent : baseEnd_111303 < baseStart_111303 := by decide
  rcases family_descends (prefixWord ++ tailWord_111303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111309 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_111309 : Nat := 118140960795 + 111309 * 2 ^ 59
def prefixEnd_111309 : Nat := 4983230072969 + 3 ^ 40 * 111309 * 2
def baseEnd_111309 : Nat := 38103345447606824483737

theorem tailTrace_111309 : CollatzResearch.WordTrace tailWord_111309 prefixEnd_111309 38103345447606824483737 := by
  unfold tailWord_111309
  simp only [CollatzResearch.WordTrace]
  refine ⟨4059772753753977908840981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2706515169169318605893987 4059772753753977908840981)
  ·
    refine ⟨190301847832217714476921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4059772753753977908840981 190301847832217714476921)
    ·
      refine ⟨142726385874163285857691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190301847832217714476921 142726385874163285857691)
      ·
        refine ⟨214089578811244928786537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142726385874163285857691 214089578811244928786537)
        ·
          refine ⟨160567184108433696589903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214089578811244928786537 160567184108433696589903)
          ·
            refine ⟨240850776162650544884855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160567184108433696589903 240850776162650544884855)
            ·
              refine ⟨361276164243975817327283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240850776162650544884855 361276164243975817327283)
              ·
                refine ⟨541914246365963725990925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361276164243975817327283 541914246365963725990925)
                ·
                  refine ⟨203217842387236397246597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 541914246365963725990925 203217842387236397246597)
                  ·
                    refine ⟨38103345447606824483737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203217842387236397246597 38103345447606824483737)
                    ·
                      rfl

theorem cell22_111309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_111309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111309 prefixEnd_111309 := by exact prefixLift 111309
  have htrace : WordTrace (prefixWord ++ tailWord_111309) baseStart_111309 baseEnd_111309 := by
    simpa [prefixWord, tailWord_111309, baseEnd_111309] using wordTrace_append hprefix tailTrace_111309
  have hstable : (prefixWord ++ tailWord_111309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111309).length < 2 ^ (prefixWord ++ tailWord_111309).sum := by decide
  have hdescent : baseEnd_111309 < baseStart_111309 := by decide
  rcases family_descends (prefixWord ++ tailWord_111309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111320 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 2, 4]
def baseStart_111320 : Nat := 118140960795 + 111320 * 2 ^ 59
def prefixEnd_111320 : Nat := 4983230072969 + 3 ^ 40 * 111320 * 2
def baseEnd_111320 : Nat := 38107110972406462458703

theorem tailTrace_111320 : CollatzResearch.WordTrace tailWord_111320 prefixEnd_111320 38107110972406462458703 := by
  unfold tailWord_111320
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030086978357063393745707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2706782637809417858327609 2030086978357063393745707)
  ·
    refine ⟨3045130467535595090618561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2030086978357063393745707 3045130467535595090618561)
    ·
      refine ⟨2283847850651696317963921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3045130467535595090618561 2283847850651696317963921)
      ·
        refine ⟨1712885887988772238472941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2283847850651696317963921 1712885887988772238472941)
        ·
          refine ⟨642332207995789589427353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1712885887988772238472941 642332207995789589427353)
          ·
            refine ⟨481749155996842192070515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642332207995789589427353 481749155996842192070515)
            ·
              refine ⟨722623733995263288105773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481749155996842192070515 722623733995263288105773)
              ·
                refine ⟨270983900248223733039665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 722623733995263288105773 270983900248223733039665)
                ·
                  refine ⟨203237925186167799779749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270983900248223733039665 203237925186167799779749)
                  ·
                    refine ⟨38107110972406462458703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203237925186167799779749 38107110972406462458703)
                    ·
                      rfl

theorem cell22_111320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_111320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111320 prefixEnd_111320 := by exact prefixLift 111320
  have htrace : WordTrace (prefixWord ++ tailWord_111320) baseStart_111320 baseEnd_111320 := by
    simpa [prefixWord, tailWord_111320, baseEnd_111320] using wordTrace_append hprefix tailTrace_111320
  have hstable : (prefixWord ++ tailWord_111320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111320).length < 2 ^ (prefixWord ++ tailWord_111320).sum := by decide
  have hdescent : baseEnd_111320 < baseStart_111320 := by decide
  rcases family_descends (prefixWord ++ tailWord_111320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111363 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 9]
def baseStart_111363 : Nat := 118140960795 + 111363 * 2 ^ 59
def prefixEnd_111363 : Nat := 4983230072969 + 3 ^ 40 * 111363 * 2
def baseEnd_111363 : Nat := 12707276917056227877857

theorem tailTrace_111363 : CollatzResearch.WordTrace tailWord_111363 prefixEnd_111363 12707276917056227877857 := by
  unfold tailWord_111363
  simp only [CollatzResearch.WordTrace]
  refine ⟨4061742295558345131306743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2707828197038896754204495 4061742295558345131306743)
  ·
    refine ⟨6092613443337517696960115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4061742295558345131306743 6092613443337517696960115)
    ·
      refine ⟨9138920165006276545440173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6092613443337517696960115 9138920165006276545440173)
      ·
        refine ⟨3427095061877353704540065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9138920165006276545440173 3427095061877353704540065)
        ·
          refine ⟨2570321296408015278405049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3427095061877353704540065 2570321296408015278405049)
          ·
            refine ⟨1927740972306011458803787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2570321296408015278405049 1927740972306011458803787)
            ·
              refine ⟨2891611458459017188205681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927740972306011458803787 2891611458459017188205681)
              ·
                refine ⟨2168708593844262891154261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2891611458459017188205681 2168708593844262891154261)
                ·
                  refine ⟨12707276917056227877857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2168708593844262891154261 12707276917056227877857)
                  ·
                    rfl

theorem cell22_111363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 9].length) (baseStart_111363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111363 prefixEnd_111363 := by exact prefixLift 111363
  have htrace : WordTrace (prefixWord ++ tailWord_111363) baseStart_111363 baseEnd_111363 := by
    simpa [prefixWord, tailWord_111363, baseEnd_111363] using wordTrace_append hprefix tailTrace_111363
  have hstable : (prefixWord ++ tailWord_111363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111363).length < 2 ^ (prefixWord ++ tailWord_111363).sum := by decide
  have hdescent : baseEnd_111363 < baseStart_111363 := by decide
  rcases family_descends (prefixWord ++ tailWord_111363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111367 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 5, 3]
def baseStart_111367 : Nat := 118140960795 + 111367 * 2 ^ 59
def prefixEnd_111367 : Nat := 4983230072969 + 3 ^ 40 * 111367 * 2
def baseEnd_111367 : Nat := 38123200032914006533559

theorem tailTrace_111367 : CollatzResearch.WordTrace tailWord_111367 prefixEnd_111367 38123200032914006533559 := by
  unfold tailWord_111367
  simp only [CollatzResearch.WordTrace]
  refine ⟨4061888187543853814452355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2707925458362569209634903 4061888187543853814452355)
  ·
    refine ⟨6092832281315780721678533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4061888187543853814452355 6092832281315780721678533)
    ·
      refine ⟨1142406052746708885314725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6092832281315780721678533 1142406052746708885314725)
      ·
        refine ⟨214201134890007915996511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1142406052746708885314725 214201134890007915996511)
        ·
          refine ⟨321301702335011873994767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214201134890007915996511 321301702335011873994767)
          ·
            refine ⟨481952553502517810992151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321301702335011873994767 481952553502517810992151)
            ·
              refine ⟨722928830253776716488227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481952553502517810992151 722928830253776716488227)
              ·
                refine ⟨1084393245380665074732341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722928830253776716488227 1084393245380665074732341)
                ·
                  refine ⟨101661866754437350756157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1084393245380665074732341 101661866754437350756157)
                  ·
                    refine ⟨38123200032914006533559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101661866754437350756157 38123200032914006533559)
                    ·
                      rfl

theorem cell22_111367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_111367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111367 prefixEnd_111367 := by exact prefixLift 111367
  have htrace : WordTrace (prefixWord ++ tailWord_111367) baseStart_111367 baseEnd_111367 := by
    simpa [prefixWord, tailWord_111367, baseEnd_111367] using wordTrace_append hprefix tailTrace_111367
  have hstable : (prefixWord ++ tailWord_111367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111367).length < 2 ^ (prefixWord ++ tailWord_111367).sum := by decide
  have hdescent : baseEnd_111367 < baseStart_111367 := by decide
  rcases family_descends (prefixWord ++ tailWord_111367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111427 : List Nat := [1, 1, 1, 3, 1, 4, 4, 2, 1, 4]
def baseStart_111427 : Nat := 118140960795 + 111427 * 2 ^ 59
def prefixEnd_111427 : Nat := 4983230072969 + 3 ^ 40 * 111427 * 2
def baseEnd_111427 : Nat := 38143739259093850033375

theorem tailTrace_111427 : CollatzResearch.WordTrace tailWord_111427 prefixEnd_111427 38143739259093850033375 := by
  unfold tailWord_111427
  simp only [CollatzResearch.WordTrace]
  refine ⟨4064076567326484061636535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2709384378217656041091023 4064076567326484061636535)
  ·
    refine ⟨6096114850989726092454803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4064076567326484061636535 6096114850989726092454803)
    ·
      refine ⟨9144172276484589138682205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6096114850989726092454803 9144172276484589138682205)
      ·
        refine ⟨3429064603681720927005827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9144172276484589138682205 3429064603681720927005827)
        ·
          refine ⟨5143596905522581390508741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3429064603681720927005827 5143596905522581390508741)
          ·
            refine ⟨964424419785484010720389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5143596905522581390508741 964424419785484010720389)
            ·
              refine ⟨180829578709778252010073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 964424419785484010720389 180829578709778252010073)
              ·
                refine ⟨135622184032333689007555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180829578709778252010073 135622184032333689007555)
                ·
                  refine ⟨203433276048500533511333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135622184032333689007555 203433276048500533511333)
                  ·
                    refine ⟨38143739259093850033375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203433276048500533511333 38143739259093850033375)
                    ·
                      rfl

theorem cell22_111427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 1, 4].length) (baseStart_111427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111427 prefixEnd_111427 := by exact prefixLift 111427
  have htrace : WordTrace (prefixWord ++ tailWord_111427) baseStart_111427 baseEnd_111427 := by
    simpa [prefixWord, tailWord_111427, baseEnd_111427] using wordTrace_append hprefix tailTrace_111427
  have hstable : (prefixWord ++ tailWord_111427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111427).length < 2 ^ (prefixWord ++ tailWord_111427).sum := by decide
  have hdescent : baseEnd_111427 < baseStart_111427 := by decide
  rcases family_descends (prefixWord ++ tailWord_111427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111440 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 1, 5]
def baseStart_111440 : Nat := 118140960795 + 111440 * 2 ^ 59
def prefixEnd_111440 : Nat := 4983230072969 + 3 ^ 40 * 111440 * 2
def baseEnd_111440 : Nat := 38148189424766149458335

theorem tailTrace_111440 : CollatzResearch.WordTrace tailWord_111440 prefixEnd_111440 38148189424766149458335 := by
  unfold tailWord_111440
  simp only [CollatzResearch.WordTrace]
  refine ⟨2032275358139693640929887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2709700477519591521239849 2032275358139693640929887)
  ·
    refine ⟨3048413037209540461394831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2032275358139693640929887 3048413037209540461394831)
    ·
      refine ⟨4572619555814310692092247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3048413037209540461394831 4572619555814310692092247)
      ·
        refine ⟨6858929333721466038138371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4572619555814310692092247 6858929333721466038138371)
        ·
          refine ⟨10288394000582199057207557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6858929333721466038138371 10288394000582199057207557)
          ·
            refine ⟨1929073875109162323226417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10288394000582199057207557 1929073875109162323226417)
            ·
              refine ⟨1446805406331871742419813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1929073875109162323226417 1446805406331871742419813)
              ·
                refine ⟨271276013687225951703715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1446805406331871742419813 271276013687225951703715)
                ·
                  refine ⟨406914020530838927555573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271276013687225951703715 406914020530838927555573)
                  ·
                    refine ⟨38148189424766149458335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 406914020530838927555573 38148189424766149458335)
                    ·
                      rfl

theorem cell22_111440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 5].length) (baseStart_111440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111440 prefixEnd_111440 := by exact prefixLift 111440
  have htrace : WordTrace (prefixWord ++ tailWord_111440) baseStart_111440 baseEnd_111440 := by
    simpa [prefixWord, tailWord_111440, baseEnd_111440] using wordTrace_append hprefix tailTrace_111440
  have hstable : (prefixWord ++ tailWord_111440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111440).length < 2 ^ (prefixWord ++ tailWord_111440).sum := by decide
  have hdescent : baseEnd_111440 < baseStart_111440 := by decide
  rcases family_descends (prefixWord ++ tailWord_111440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111485 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_111485 : Nat := 118140960795 + 111485 * 2 ^ 59
def prefixEnd_111485 : Nat := 4983230072969 + 3 ^ 40 * 111485 * 2
def baseEnd_111485 : Nat := 38163593844401032083197

theorem tailTrace_111485 : CollatzResearch.WordTrace tailWord_111485 prefixEnd_111485 38163593844401032083197 := by
  unfold tailWord_111485
  simp only [CollatzResearch.WordTrace]
  refine ⟨4066192001116359967247909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2710794667410906644831939 4066192001116359967247909)
  ·
    refine ⟨762411000209317493858983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4066192001116359967247909 762411000209317493858983)
    ·
      refine ⟨1143616500313976240788475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 762411000209317493858983 1143616500313976240788475)
      ·
        refine ⟨1715424750470964361182713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143616500313976240788475 1715424750470964361182713)
        ·
          refine ⟨1286568562853223270887035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1715424750470964361182713 1286568562853223270887035)
          ·
            refine ⟨1929852844279834906330553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286568562853223270887035 1929852844279834906330553)
            ·
              refine ⟨1447389633209876179747915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1929852844279834906330553 1447389633209876179747915)
              ·
                refine ⟨2171084449814814269621873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1447389633209876179747915 2171084449814814269621873)
                ·
                  refine ⟨1628313337361110702216405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2171084449814814269621873 1628313337361110702216405)
                  ·
                    refine ⟨38163593844401032083197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1628313337361110702216405 38163593844401032083197)
                    ·
                      rfl

theorem cell22_111485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_111485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111485 prefixEnd_111485 := by exact prefixLift 111485
  have htrace : WordTrace (prefixWord ++ tailWord_111485) baseStart_111485 baseEnd_111485 := by
    simpa [prefixWord, tailWord_111485, baseEnd_111485] using wordTrace_append hprefix tailTrace_111485
  have hstable : (prefixWord ++ tailWord_111485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111485).length < 2 ^ (prefixWord ++ tailWord_111485).sum := by decide
  have hdescent : baseEnd_111485 < baseStart_111485 := by decide
  rcases family_descends (prefixWord ++ tailWord_111485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111510 : List Nat := [5, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_111510 : Nat := 118140960795 + 111510 * 2 ^ 59
def prefixEnd_111510 : Nat := 4983230072969 + 3 ^ 40 * 111510 * 2
def baseEnd_111510 : Nat := 12724050618436433402707

theorem tailTrace_111510 : CollatzResearch.WordTrace tailWord_111510 prefixEnd_111510 12724050618436433402707 := by
  unfold tailWord_111510
  simp only [CollatzResearch.WordTrace]
  refine ⟨254193989126611827306749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2711402550683859491271989 254193989126611827306749)
  ·
    refine ⟨95322745922479435240031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254193989126611827306749 95322745922479435240031)
    ·
      refine ⟨142984118883719152860047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95322745922479435240031 142984118883719152860047)
      ·
        refine ⟨214476178325578729290071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142984118883719152860047 214476178325578729290071)
        ·
          refine ⟨321714267488368093935107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214476178325578729290071 321714267488368093935107)
          ·
            refine ⟨482571401232552140902661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321714267488368093935107 482571401232552140902661)
            ·
              refine ⟨90482137731103526419249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 482571401232552140902661 90482137731103526419249)
              ·
                refine ⟨67861603298327644814437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90482137731103526419249 67861603298327644814437)
                ·
                  refine ⟨12724050618436433402707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67861603298327644814437 12724050618436433402707)
                  ·
                    rfl

theorem cell22_111510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_111510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111510 prefixEnd_111510 := by exact prefixLift 111510
  have htrace : WordTrace (prefixWord ++ tailWord_111510) baseStart_111510 baseEnd_111510 := by
    simpa [prefixWord, tailWord_111510, baseEnd_111510] using wordTrace_append hprefix tailTrace_111510
  have hstable : (prefixWord ++ tailWord_111510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111510).length < 2 ^ (prefixWord ++ tailWord_111510).sum := by decide
  have hdescent : baseEnd_111510 < baseStart_111510 := by decide
  rcases family_descends (prefixWord ++ tailWord_111510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111577 : List Nat := [1, 2, 1, 2, 5, 1, 1, 3, 6]
def baseStart_111577 : Nat := 118140960795 + 111577 * 2 ^ 59
def prefixEnd_111577 : Nat := 4983230072969 + 3 ^ 40 * 111577 * 2
def baseEnd_111577 : Nat := 12731695774847819594305

theorem tailTrace_111577 : CollatzResearch.WordTrace tailWord_111577 prefixEnd_111577 12731695774847819594305 := by
  unfold tailWord_111577
  simp only [CollatzResearch.WordTrace]
  refine ⟨4069547516783059679596985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2713031677855373119731323 4069547516783059679596985)
  ·
    refine ⟨3052160637587294759697739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4069547516783059679596985 3052160637587294759697739)
    ·
      refine ⟨4578240956380942139546609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3052160637587294759697739 4578240956380942139546609)
      ·
        refine ⟨3433680717285706604659957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4578240956380942139546609 3433680717285706604659957)
        ·
          refine ⟨321907567245534994186871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3433680717285706604659957 321907567245534994186871)
          ·
            refine ⟨482861350868302491280307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321907567245534994186871 482861350868302491280307)
            ·
              refine ⟨724292026302453736920461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482861350868302491280307 724292026302453736920461)
              ·
                refine ⟨271609509863420151345173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 724292026302453736920461 271609509863420151345173)
                ·
                  refine ⟨12731695774847819594305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 271609509863420151345173 12731695774847819594305)
                  ·
                    rfl

theorem cell22_111577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_111577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111577 prefixEnd_111577 := by exact prefixLift 111577
  have htrace : WordTrace (prefixWord ++ tailWord_111577) baseStart_111577 baseEnd_111577 := by
    simpa [prefixWord, tailWord_111577, baseEnd_111577] using wordTrace_append hprefix tailTrace_111577
  have hstable : (prefixWord ++ tailWord_111577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111577).length < 2 ^ (prefixWord ++ tailWord_111577).sum := by decide
  have hdescent : baseEnd_111577 < baseStart_111577 := by decide
  rcases family_descends (prefixWord ++ tailWord_111577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111624 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 2, 4]
def baseStart_111624 : Nat := 118140960795 + 111624 * 2 ^ 59
def prefixEnd_111624 : Nat := 4983230072969 + 3 ^ 40 * 111624 * 2
def baseEnd_111624 : Nat := 38211176385051002857771

theorem tailTrace_111624 : CollatzResearch.WordTrace tailWord_111624 prefixEnd_111624 38211176385051002857771 := by
  unfold tailWord_111624
  simp only [CollatzResearch.WordTrace]
  refine ⟨2035630873806393353278963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2714174498408524471038617 2035630873806393353278963)
  ·
    refine ⟨3053446310709590029918445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2035630873806393353278963 3053446310709590029918445)
    ·
      refine ⟨1145042366516096261219417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3053446310709590029918445 1145042366516096261219417)
      ·
        refine ⟨858781774887072195914563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1145042366516096261219417 858781774887072195914563)
        ·
          refine ⟨1288172662330608293871845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858781774887072195914563 1288172662330608293871845)
          ·
            refine ⟨241532374186989055100971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1288172662330608293871845 241532374186989055100971)
            ·
              refine ⟨362298561280483582651457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241532374186989055100971 362298561280483582651457)
              ·
                refine ⟨271723920960362686988593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362298561280483582651457 271723920960362686988593)
                ·
                  refine ⟨203792940720272015241445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 271723920960362686988593 203792940720272015241445)
                  ·
                    refine ⟨38211176385051002857771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203792940720272015241445 38211176385051002857771)
                    ·
                      rfl

theorem cell22_111624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_111624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111624 prefixEnd_111624 := by exact prefixLift 111624
  have htrace : WordTrace (prefixWord ++ tailWord_111624) baseStart_111624 baseEnd_111624 := by
    simpa [prefixWord, tailWord_111624, baseEnd_111624] using wordTrace_append hprefix tailTrace_111624
  have hstable : (prefixWord ++ tailWord_111624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111624).length < 2 ^ (prefixWord ++ tailWord_111624).sum := by decide
  have hdescent : baseEnd_111624 < baseStart_111624 := by decide
  rcases family_descends (prefixWord ++ tailWord_111624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111639 : List Nat := [1, 1, 3, 5, 1, 2, 2, 7]
def baseStart_111639 : Nat := 118140960795 + 111639 * 2 ^ 59
def prefixEnd_111639 : Nat := 4983230072969 + 3 ^ 40 * 111639 * 2
def baseEnd_111639 : Nat := 4246256799066218192525

theorem tailTrace_111639 : CollatzResearch.WordTrace tailWord_111639 prefixEnd_111639 4246256799066218192525 := by
  unfold tailWord_111639
  simp only [CollatzResearch.WordTrace]
  refine ⟨4071808842558444268353971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2714539228372296178902647 4071808842558444268353971)
  ·
    refine ⟨6107713263837666402530957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4071808842558444268353971 6107713263837666402530957)
    ·
      refine ⟨2290392473939124900949109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6107713263837666402530957 2290392473939124900949109)
      ·
        refine ⟨214724294431792959463979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2290392473939124900949109 214724294431792959463979)
        ·
          refine ⟨322086441647689439195969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214724294431792959463979 322086441647689439195969)
          ·
            refine ⟨241564831235767079396977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322086441647689439195969 241564831235767079396977)
            ·
              refine ⟨181173623426825309547733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241564831235767079396977 181173623426825309547733)
              ·
                refine ⟨4246256799066218192525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 181173623426825309547733 4246256799066218192525)
                ·
                  rfl

theorem cell22_111639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 7].length) (baseStart_111639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111639 prefixEnd_111639 := by exact prefixLift 111639
  have htrace : WordTrace (prefixWord ++ tailWord_111639) baseStart_111639 baseEnd_111639 := by
    simpa [prefixWord, tailWord_111639, baseEnd_111639] using wordTrace_append hprefix tailTrace_111639
  have hstable : (prefixWord ++ tailWord_111639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111639).length < 2 ^ (prefixWord ++ tailWord_111639).sum := by decide
  have hdescent : baseEnd_111639 < baseStart_111639 := by decide
  rcases family_descends (prefixWord ++ tailWord_111639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111671 : List Nat := [1, 1, 3, 1, 2, 2, 1, 7, 1, 3]
def baseStart_111671 : Nat := 118140960795 + 111671 * 2 ^ 59
def prefixEnd_111671 : Nat := 4983230072969 + 3 ^ 40 * 111671 * 2
def baseEnd_111671 : Nat := 38227265445558546932627

theorem tailTrace_111671 : CollatzResearch.WordTrace tailWord_111671 prefixEnd_111671 38227265445558546932627 := by
  unfold tailWord_111671
  simp only [CollatzResearch.WordTrace]
  refine ⟨4072975978442513733518867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2715317318961675822345911 4072975978442513733518867)
  ·
    refine ⟨6109463967663770600278301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4072975978442513733518867 6109463967663770600278301)
    ·
      refine ⟨2291048987873913975104363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6109463967663770600278301 2291048987873913975104363)
      ·
        refine ⟨3436573481810870962656545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2291048987873913975104363 3436573481810870962656545)
        ·
          refine ⟨2577430111358153221992409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3436573481810870962656545 2577430111358153221992409)
          ·
            refine ⟨1933072583518614916494307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2577430111358153221992409 1933072583518614916494307)
            ·
              refine ⟨2899608875277922374741461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933072583518614916494307 2899608875277922374741461)
              ·
                refine ⟨67959583014326305658003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2899608875277922374741461 67959583014326305658003)
                ·
                  refine ⟨101939374521489458487005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67959583014326305658003 101939374521489458487005)
                  ·
                    refine ⟨38227265445558546932627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101939374521489458487005 38227265445558546932627)
                    ·
                      rfl

theorem cell22_111671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_111671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111671 prefixEnd_111671 := by exact prefixLift 111671
  have htrace : WordTrace (prefixWord ++ tailWord_111671) baseStart_111671 baseEnd_111671 := by
    simpa [prefixWord, tailWord_111671, baseEnd_111671] using wordTrace_append hprefix tailTrace_111671
  have hstable : (prefixWord ++ tailWord_111671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111671).length < 2 ^ (prefixWord ++ tailWord_111671).sum := by decide
  have hdescent : baseEnd_111671 < baseStart_111671 := by decide
  rcases family_descends (prefixWord ++ tailWord_111671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111686 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_111686 : Nat := 118140960795 + 111686 * 2 ^ 59
def prefixEnd_111686 : Nat := 4983230072969 + 3 ^ 40 * 111686 * 2
def baseEnd_111686 : Nat := 38232400252103507807581

theorem tailTrace_111686 : CollatzResearch.WordTrace tailWord_111686 prefixEnd_111686 38232400252103507807581 := by
  unfold tailWord_111686
  simp only [CollatzResearch.WordTrace]
  refine ⟨127297596043380352978591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2715682048925447530209941 127297596043380352978591)
  ·
    refine ⟨190946394065070529467887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127297596043380352978591 190946394065070529467887)
    ·
      refine ⟨286419591097605794201831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190946394065070529467887 286419591097605794201831)
      ·
        refine ⟨429629386646408691302747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286419591097605794201831 429629386646408691302747)
        ·
          refine ⟨644444079969613036954121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429629386646408691302747 644444079969613036954121)
          ·
            refine ⟨483333059977209777715591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644444079969613036954121 483333059977209777715591)
            ·
              refine ⟨724999589965814666573387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483333059977209777715591 724999589965814666573387)
              ·
                refine ⟨1087499384948721999860081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 724999589965814666573387 1087499384948721999860081)
                ·
                  refine ⟨815624538711541499895061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1087499384948721999860081 815624538711541499895061)
                  ·
                    refine ⟨38232400252103507807581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 815624538711541499895061 38232400252103507807581)
                    ·
                      rfl

theorem cell22_111686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_111686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111686 prefixEnd_111686 := by exact prefixLift 111686
  have htrace : WordTrace (prefixWord ++ tailWord_111686) baseStart_111686 baseEnd_111686 := by
    simpa [prefixWord, tailWord_111686, baseEnd_111686] using wordTrace_append hprefix tailTrace_111686
  have hstable : (prefixWord ++ tailWord_111686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111686).length < 2 ^ (prefixWord ++ tailWord_111686).sum := by decide
  have hdescent : baseEnd_111686 < baseStart_111686 := by decide
  rcases family_descends (prefixWord ++ tailWord_111686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111812 : List Nat := [2, 3, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_111812 : Nat := 118140960795 + 111812 * 2 ^ 59
def prefixEnd_111812 : Nat := 4983230072969 + 3 ^ 40 * 111812 * 2
def baseEnd_111812 : Nat := 38275532627081179157195

theorem tailTrace_111812 : CollatzResearch.WordTrace tailWord_111812 prefixEnd_111812 38275532627081179157195 := by
  unfold tailWord_111812
  simp only [CollatzResearch.WordTrace]
  refine ⟨2039059335465847407200845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2718745780621129876267793 2039059335465847407200845)
  ·
    refine ⟨764647250799692777700317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2039059335465847407200845 764647250799692777700317)
    ·
      refine ⟨286742719049884791637619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 764647250799692777700317 286742719049884791637619)
      ·
        refine ⟨430114078574827187456429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286742719049884791637619 430114078574827187456429)
        ·
          refine ⟨161292779465560195296161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 430114078574827187456429 161292779465560195296161)
          ·
            refine ⟨120969584599170146472121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161292779465560195296161 120969584599170146472121)
            ·
              refine ⟨90727188449377609854091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120969584599170146472121 90727188449377609854091)
              ·
                refine ⟨136090782674066414781137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90727188449377609854091 136090782674066414781137)
                ·
                  refine ⟨102068087005549811085853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136090782674066414781137 102068087005549811085853)
                  ·
                    refine ⟨38275532627081179157195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102068087005549811085853 38275532627081179157195)
                    ·
                      rfl

theorem cell22_111812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_111812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111812 prefixEnd_111812 := by exact prefixLift 111812
  have htrace : WordTrace (prefixWord ++ tailWord_111812) baseStart_111812 baseEnd_111812 := by
    simpa [prefixWord, tailWord_111812, baseEnd_111812] using wordTrace_append hprefix tailTrace_111812
  have hstable : (prefixWord ++ tailWord_111812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111812).length < 2 ^ (prefixWord ++ tailWord_111812).sum := by decide
  have hdescent : baseEnd_111812 < baseStart_111812 := by decide
  rcases family_descends (prefixWord ++ tailWord_111812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111834 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_111834 : Nat := 118140960795 + 111834 * 2 ^ 59
def prefixEnd_111834 : Nat := 4983230072969 + 3 ^ 40 * 111834 * 2
def baseEnd_111834 : Nat := 38283063676680455107127

theorem tailTrace_111834 : CollatzResearch.WordTrace tailWord_111834 prefixEnd_111834 38283063676680455107127 := by
  unfold tailWord_111834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1019730269212998142925639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2719280717901328381135037 1019730269212998142925639)
  ·
    refine ⟨1529595403819497214388459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1019730269212998142925639 1529595403819497214388459)
    ·
      refine ⟨2294393105729245821582689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1529595403819497214388459 2294393105729245821582689)
      ·
        refine ⟨1720794829296934366187017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2294393105729245821582689 1720794829296934366187017)
        ·
          refine ⟨1290596121972700774640263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1720794829296934366187017 1290596121972700774640263)
          ·
            refine ⟨1935894182959051161960395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1290596121972700774640263 1935894182959051161960395)
            ·
              refine ⟨2903841274438576742940593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1935894182959051161960395 2903841274438576742940593)
              ·
                refine ⟨2177880955828932557205445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2903841274438576742940593 2177880955828932557205445)
                ·
                  refine ⟨408352679217924854476021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2177880955828932557205445 408352679217924854476021)
                  ·
                    refine ⟨38283063676680455107127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 408352679217924854476021 38283063676680455107127)
                    ·
                      rfl

theorem cell22_111834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_111834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111834 prefixEnd_111834 := by exact prefixLift 111834
  have htrace : WordTrace (prefixWord ++ tailWord_111834) baseStart_111834 baseEnd_111834 := by
    simpa [prefixWord, tailWord_111834, baseEnd_111834] using wordTrace_append hprefix tailTrace_111834
  have hstable : (prefixWord ++ tailWord_111834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111834).length < 2 ^ (prefixWord ++ tailWord_111834).sum := by decide
  have hdescent : baseEnd_111834 < baseStart_111834 := by decide
  rcases family_descends (prefixWord ++ tailWord_111834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111849 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 7, 4]
def baseStart_111849 : Nat := 118140960795 + 111849 * 2 ^ 59
def prefixEnd_111849 : Nat := 4983230072969 + 3 ^ 40 * 111849 * 2
def baseEnd_111849 : Nat := 38288198483225415982081

theorem tailTrace_111849 : CollatzResearch.WordTrace tailWord_111849 prefixEnd_111849 38288198483225415982081 := by
  unfold tailWord_111849
  simp only [CollatzResearch.WordTrace]
  refine ⟨4079468171797650133498601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2719645447865100088999067 4079468171797650133498601)
  ·
    refine ⟨3059601128848237600123951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4079468171797650133498601 3059601128848237600123951)
    ·
      refine ⟨4589401693272356400185927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3059601128848237600123951 4589401693272356400185927)
      ·
        refine ⟨6884102539908534600278891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4589401693272356400185927 6884102539908534600278891)
        ·
          refine ⟨10326153809862801900418337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6884102539908534600278891 10326153809862801900418337)
          ·
            refine ⟨7744615357397101425313753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10326153809862801900418337 7744615357397101425313753)
            ·
              refine ⟨5808461518047826068985315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7744615357397101425313753 5808461518047826068985315)
              ·
                refine ⟨8712692277071739103477973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5808461518047826068985315 8712692277071739103477973)
                ·
                  refine ⟨204203725243868885237765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8712692277071739103477973 204203725243868885237765)
                  ·
                    refine ⟨38288198483225415982081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204203725243868885237765 38288198483225415982081)
                    ·
                      rfl

theorem cell22_111849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_111849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111849 prefixEnd_111849 := by exact prefixLift 111849
  have htrace : WordTrace (prefixWord ++ tailWord_111849) baseStart_111849 baseEnd_111849 := by
    simpa [prefixWord, tailWord_111849, baseEnd_111849] using wordTrace_append hprefix tailTrace_111849
  have hstable : (prefixWord ++ tailWord_111849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111849).length < 2 ^ (prefixWord ++ tailWord_111849).sum := by decide
  have hdescent : baseEnd_111849 < baseStart_111849 := by decide
  rcases family_descends (prefixWord ++ tailWord_111849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111853 : List Nat := [1, 5, 1, 2, 2, 2, 2, 2, 5]
def baseStart_111853 : Nat := 118140960795 + 111853 * 2 ^ 59
def prefixEnd_111853 : Nat := 4983230072969 + 3 ^ 40 * 111853 * 2
def baseEnd_111853 : Nat := 12763189254990246294023

theorem tailTrace_111853 : CollatzResearch.WordTrace tailWord_111853 prefixEnd_111853 12763189254990246294023 := by
  unfold tailWord_111853
  simp only [CollatzResearch.WordTrace]
  refine ⟨4079614063783158816644213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2719742709188772544429475 4079614063783158816644213)
  ·
    refine ⟨382463818479671139060395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4079614063783158816644213 382463818479671139060395)
    ·
      refine ⟨573695727719506708590593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382463818479671139060395 573695727719506708590593)
      ·
        refine ⟨430271795789630031442945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573695727719506708590593 430271795789630031442945)
        ·
          refine ⟨322703846842222523582209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430271795789630031442945 322703846842222523582209)
          ·
            refine ⟨242027885131666892686657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322703846842222523582209 242027885131666892686657)
            ·
              refine ⟨181520913848750169514993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242027885131666892686657 181520913848750169514993)
              ·
                refine ⟨136140685386562627136245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181520913848750169514993 136140685386562627136245)
                ·
                  refine ⟨12763189254990246294023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136140685386562627136245 12763189254990246294023)
                  ·
                    rfl

theorem cell22_111853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_111853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111853 prefixEnd_111853 := by exact prefixLift 111853
  have htrace : WordTrace (prefixWord ++ tailWord_111853) baseStart_111853 baseEnd_111853 := by
    simpa [prefixWord, tailWord_111853, baseEnd_111853] using wordTrace_append hprefix tailTrace_111853
  have hstable : (prefixWord ++ tailWord_111853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111853).length < 2 ^ (prefixWord ++ tailWord_111853).sum := by decide
  have hdescent : baseEnd_111853 < baseStart_111853 := by decide
  rcases family_descends (prefixWord ++ tailWord_111853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111896 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 1, 5]
def baseStart_111896 : Nat := 118140960795 + 111896 * 2 ^ 59
def prefixEnd_111896 : Nat := 4983230072969 + 3 ^ 40 * 111896 * 2
def baseEnd_111896 : Nat := 38304287543732960056937

theorem tailTrace_111896 : CollatzResearch.WordTrace tailWord_111896 prefixEnd_111896 38304287543732960056937 := by
  unfold tailWord_111896
  simp only [CollatzResearch.WordTrace]
  refine ⟨2040591201313688580229771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2720788268418251440306361 2040591201313688580229771)
  ·
    refine ⟨3060886801970532870344657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2040591201313688580229771 3060886801970532870344657)
    ·
      refine ⟨2295665101477899652758493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3060886801970532870344657 2295665101477899652758493)
      ·
        refine ⟨860874413054212369784435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2295665101477899652758493 860874413054212369784435)
        ·
          refine ⟨1291311619581318554676653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860874413054212369784435 1291311619581318554676653)
          ·
            refine ⟨484241857342994458003745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1291311619581318554676653 484241857342994458003745)
            ·
              refine ⟨363181393007245843502809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484241857342994458003745 363181393007245843502809)
              ·
                refine ⟨272386044755434382627107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363181393007245843502809 272386044755434382627107)
                ·
                  refine ⟨408579067133151573940661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272386044755434382627107 408579067133151573940661)
                  ·
                    refine ⟨38304287543732960056937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 408579067133151573940661 38304287543732960056937)
                    ·
                      rfl

theorem cell22_111896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_111896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111896 prefixEnd_111896 := by exact prefixLift 111896
  have htrace : WordTrace (prefixWord ++ tailWord_111896) baseStart_111896 baseEnd_111896 := by
    simpa [prefixWord, tailWord_111896, baseEnd_111896] using wordTrace_append hprefix tailTrace_111896
  have hstable : (prefixWord ++ tailWord_111896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111896).length < 2 ^ (prefixWord ++ tailWord_111896).sum := by decide
  have hdescent : baseEnd_111896 < baseStart_111896 := by decide
  rcases family_descends (prefixWord ++ tailWord_111896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111898 : List Nat := [3, 1, 1, 3, 3, 1, 1, 5, 4]
def baseStart_111898 : Nat := 118140960795 + 111898 * 2 ^ 59
def prefixEnd_111898 : Nat := 4983230072969 + 3 ^ 40 * 111898 * 2
def baseEnd_111898 : Nat := 12768324061535207168977

theorem tailTrace_111898 : CollatzResearch.WordTrace tailWord_111898 prefixEnd_111898 12768324061535207168977 := by
  unfold tailWord_111898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1020313837155032875508087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2720836899080087668021565 1020313837155032875508087)
  ·
    refine ⟨1530470755732549313262131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1020313837155032875508087 1530470755732549313262131)
    ·
      refine ⟨2295706133598823969893197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1530470755732549313262131 2295706133598823969893197)
      ·
        refine ⟨860889800099558988709949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2295706133598823969893197 860889800099558988709949)
        ·
          refine ⟨322833675037334620766231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 860889800099558988709949 322833675037334620766231)
          ·
            refine ⟨484250512556001931149347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322833675037334620766231 484250512556001931149347)
            ·
              refine ⟨726375768834002896724021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484250512556001931149347 726375768834002896724021)
              ·
                refine ⟨68097728328187771567877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 726375768834002896724021 68097728328187771567877)
                ·
                  refine ⟨12768324061535207168977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68097728328187771567877 12768324061535207168977)
                  ·
                    rfl

theorem cell22_111898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_111898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111898 prefixEnd_111898 := by exact prefixLift 111898
  have htrace : WordTrace (prefixWord ++ tailWord_111898) baseStart_111898 baseEnd_111898 := by
    simpa [prefixWord, tailWord_111898, baseEnd_111898] using wordTrace_append hprefix tailTrace_111898
  have hstable : (prefixWord ++ tailWord_111898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111898).length < 2 ^ (prefixWord ++ tailWord_111898).sum := by decide
  have hdescent : baseEnd_111898 < baseStart_111898 := by decide
  rcases family_descends (prefixWord ++ tailWord_111898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111930 : List Nat := [3, 1, 1, 1, 4, 1, 5, 1, 2, 3]
def baseStart_111930 : Nat := 118140960795 + 111930 * 2 ^ 59
def prefixEnd_111930 : Nat := 4983230072969 + 3 ^ 40 * 111930 * 2
def baseEnd_111930 : Nat := 38315926438568204706833

theorem tailTrace_111930 : CollatzResearch.WordTrace tailWord_111930 prefixEnd_111930 38315926438568204706833 := by
  unfold tailWord_111930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1020605621126050241799311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2721614989669467311464829 1020605621126050241799311)
  ·
    refine ⟨1530908431689075362698967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1020605621126050241799311 1530908431689075362698967)
    ·
      refine ⟨2296362647533613044048451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1530908431689075362698967 2296362647533613044048451)
      ·
        refine ⟨3444543971300419566072677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296362647533613044048451 3444543971300419566072677)
        ·
          refine ⟨645851994618828668638627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3444543971300419566072677 645851994618828668638627)
          ·
            refine ⟨968777991928243002957941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645851994618828668638627 968777991928243002957941)
            ·
              refine ⟨90822936743272781527307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 968777991928243002957941 90822936743272781527307)
              ·
                refine ⟨136234405114909172290961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90822936743272781527307 136234405114909172290961)
                ·
                  refine ⟨102175803836181879218221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136234405114909172290961 102175803836181879218221)
                  ·
                    refine ⟨38315926438568204706833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102175803836181879218221 38315926438568204706833)
                    ·
                      rfl

theorem cell22_111930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_111930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111930 prefixEnd_111930 := by exact prefixLift 111930
  have htrace : WordTrace (prefixWord ++ tailWord_111930) baseStart_111930 baseEnd_111930 := by
    simpa [prefixWord, tailWord_111930, baseEnd_111930] using wordTrace_append hprefix tailTrace_111930
  have hstable : (prefixWord ++ tailWord_111930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111930).length < 2 ^ (prefixWord ++ tailWord_111930).sum := by decide
  have hdescent : baseEnd_111930 < baseStart_111930 := by decide
  rcases family_descends (prefixWord ++ tailWord_111930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111943 : List Nat := [1, 1, 4, 1, 2, 5, 2, 6]
def baseStart_111943 : Nat := 118140960795 + 111943 * 2 ^ 59
def prefixEnd_111943 : Nat := 4983230072969 + 3 ^ 40 * 111943 * 2
def baseEnd_111943 : Nat := 4257819622693389347977

theorem tailTrace_111943 : CollatzResearch.WordTrace tailWord_111943 prefixEnd_111943 4257819622693389347977 := by
  unfold tailWord_111943
  simp only [CollatzResearch.WordTrace]
  refine ⟨4082896633457104187420483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2721931088971402791613655 4082896633457104187420483)
  ·
    refine ⟨6124344950185656281130725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4082896633457104187420483 6124344950185656281130725)
    ·
      refine ⟨1148314678159810552712011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6124344950185656281130725 1148314678159810552712011)
      ·
        refine ⟨1722472017239715829068017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1148314678159810552712011 1722472017239715829068017)
        ·
          refine ⟨1291854012929786871801013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1722472017239715829068017 1291854012929786871801013)
          ·
            refine ⟨121111313712167519231345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1291854012929786871801013 121111313712167519231345)
            ·
              refine ⟨90833485284125639423509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121111313712167519231345 90833485284125639423509)
              ·
                refine ⟨4257819622693389347977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90833485284125639423509 4257819622693389347977)
                ·
                  rfl

theorem cell22_111943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 6].length) (baseStart_111943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111943 prefixEnd_111943 := by exact prefixLift 111943
  have htrace : WordTrace (prefixWord ++ tailWord_111943) baseStart_111943 baseEnd_111943 := by
    simpa [prefixWord, tailWord_111943, baseEnd_111943] using wordTrace_append hprefix tailTrace_111943
  have hstable : (prefixWord ++ tailWord_111943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111943).length < 2 ^ (prefixWord ++ tailWord_111943).sum := by decide
  have hdescent : baseEnd_111943 < baseStart_111943 := by decide
  rcases family_descends (prefixWord ++ tailWord_111943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111949 : List Nat := [1, 6, 1, 3, 1, 2, 1, 3, 4]
def baseStart_111949 : Nat := 118140960795 + 111949 * 2 ^ 59
def prefixEnd_111949 : Nat := 4983230072969 + 3 ^ 40 * 111949 * 2
def baseEnd_111949 : Nat := 12774143508952829493925

theorem tailTrace_111949 : CollatzResearch.WordTrace tailWord_111949 prefixEnd_111949 12774143508952829493925 := by
  unfold tailWord_111949
  simp only [CollatzResearch.WordTrace]
  refine ⟨4083115471435367212138901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2722076980956911474759267 4083115471435367212138901)
  ·
    refine ⟨191396037723532838069011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4083115471435367212138901 191396037723532838069011)
    ·
      refine ⟨287094056585299257103517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191396037723532838069011 287094056585299257103517)
      ·
        refine ⟨107660271219487221413819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287094056585299257103517 107660271219487221413819)
        ·
          refine ⟨161490406829230832120729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107660271219487221413819 161490406829230832120729)
          ·
            refine ⟨121117805121923124090547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161490406829230832120729 121117805121923124090547)
            ·
              refine ⟨181676707682884686135821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121117805121923124090547 181676707682884686135821)
              ·
                refine ⟨68128765381081757300933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181676707682884686135821 68128765381081757300933)
                ·
                  refine ⟨12774143508952829493925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68128765381081757300933 12774143508952829493925)
                  ·
                    rfl

theorem cell22_111949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_111949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111949 prefixEnd_111949 := by exact prefixLift 111949
  have htrace : WordTrace (prefixWord ++ tailWord_111949) baseStart_111949 baseEnd_111949 := by
    simpa [prefixWord, tailWord_111949, baseEnd_111949] using wordTrace_append hprefix tailTrace_111949
  have hstable : (prefixWord ++ tailWord_111949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111949).length < 2 ^ (prefixWord ++ tailWord_111949).sum := by decide
  have hdescent : baseEnd_111949 < baseStart_111949 := by decide
  rcases family_descends (prefixWord ++ tailWord_111949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111971 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 7]
def baseStart_111971 : Nat := 118140960795 + 111971 * 2 ^ 59
def prefixEnd_111971 : Nat := 4983230072969 + 3 ^ 40 * 111971 * 2
def baseEnd_111971 : Nat := 12776653858819254810569

theorem tailTrace_111971 : CollatzResearch.WordTrace tailWord_111971 prefixEnd_111971 12776653858819254810569 := by
  unfold tailWord_111971
  simp only [CollatzResearch.WordTrace]
  refine ⟨4083917877355664969439767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2722611918237109979626511 4083917877355664969439767)
  ·
    refine ⟨6125876816033497454159651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4083917877355664969439767 6125876816033497454159651)
    ·
      refine ⟨9188815224050246181239477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6125876816033497454159651 9188815224050246181239477)
      ·
        refine ⟨861451427254710579491201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9188815224050246181239477 861451427254710579491201)
        ·
          refine ⟨646088570441032934618401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 861451427254710579491201 646088570441032934618401)
          ·
            refine ⟨484566427830774700963801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 646088570441032934618401 484566427830774700963801)
            ·
              refine ⟨363424820873081025722851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484566427830774700963801 363424820873081025722851)
              ·
                refine ⟨545137231309621538584277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363424820873081025722851 545137231309621538584277)
                ·
                  refine ⟨12776653858819254810569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 545137231309621538584277 12776653858819254810569)
                  ·
                    rfl

theorem cell22_111971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 7].length) (baseStart_111971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111971 prefixEnd_111971 := by exact prefixLift 111971
  have htrace : WordTrace (prefixWord ++ tailWord_111971) baseStart_111971 baseEnd_111971 := by
    simpa [prefixWord, tailWord_111971, baseEnd_111971] using wordTrace_append hprefix tailTrace_111971
  have hstable : (prefixWord ++ tailWord_111971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111971).length < 2 ^ (prefixWord ++ tailWord_111971).sum := by decide
  have hdescent : baseEnd_111971 < baseStart_111971 := by decide
  rcases family_descends (prefixWord ++ tailWord_111971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111986 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_111986 : Nat := 118140960795 + 111986 * 2 ^ 59
def prefixEnd_111986 : Nat := 4983230072969 + 3 ^ 40 * 111986 * 2
def baseEnd_111986 : Nat := 38335096383002725306661

theorem tailTrace_111986 : CollatzResearch.WordTrace tailWord_111986 prefixEnd_111986 38335096383002725306661 := by
  unfold tailWord_111986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1021116243075330632808953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2722976648200881687490541 1021116243075330632808953)
  ·
    refine ⟨765837182306497974606715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1021116243075330632808953 765837182306497974606715)
    ·
      refine ⟨1148755773459746961910073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 765837182306497974606715 1148755773459746961910073)
      ·
        refine ⟨861566830094810221432555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1148755773459746961910073 861566830094810221432555)
        ·
          refine ⟨1292350245142215332148833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861566830094810221432555 1292350245142215332148833)
          ·
            refine ⟨969262683856661499111625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1292350245142215332148833 969262683856661499111625)
            ·
              refine ⟨726947012892496124333719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 969262683856661499111625 726947012892496124333719)
              ·
                refine ⟨1090420519338744186500579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 726947012892496124333719 1090420519338744186500579)
                ·
                  refine ⟨1635630779008116279750869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1090420519338744186500579 1635630779008116279750869)
                  ·
                    refine ⟨38335096383002725306661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1635630779008116279750869 38335096383002725306661)
                    ·
                      rfl

theorem cell22_111986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_111986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_111986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_111986 prefixEnd_111986 := by exact prefixLift 111986
  have htrace : WordTrace (prefixWord ++ tailWord_111986) baseStart_111986 baseEnd_111986 := by
    simpa [prefixWord, tailWord_111986, baseEnd_111986] using wordTrace_append hprefix tailTrace_111986
  have hstable : (prefixWord ++ tailWord_111986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111986).length < 2 ^ (prefixWord ++ tailWord_111986).sum := by decide
  have hdescent : baseEnd_111986 < baseStart_111986 := by decide
  rcases family_descends (prefixWord ++ tailWord_111986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112110 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_112110 : Nat := 118140960795 + 112110 * 2 ^ 59
def prefixEnd_112110 : Nat := 4983230072969 + 3 ^ 40 * 112110 * 2
def baseEnd_112110 : Nat := 38377544117107735206281

theorem tailTrace_112110 : CollatzResearch.WordTrace tailWord_112110 prefixEnd_112110 38377544117107735206281 := by
  unfold tailWord_112110
  simp only [CollatzResearch.WordTrace]
  refine ⟨511123452981511463593723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2725991749234727805833189 511123452981511463593723)
  ·
    refine ⟨766685179472267195390585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 511123452981511463593723 766685179472267195390585)
    ·
      refine ⟨575013884604200396542939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 766685179472267195390585 575013884604200396542939)
      ·
        refine ⟨862520826906300594814409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575013884604200396542939 862520826906300594814409)
        ·
          refine ⟨646890620179725446110807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 862520826906300594814409 646890620179725446110807)
          ·
            refine ⟨970335930269588169166211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646890620179725446110807 970335930269588169166211)
            ·
              refine ⟨1455503895404382253749317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970335930269588169166211 1455503895404382253749317)
              ·
                refine ⟨272906980388321672577997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1455503895404382253749317 272906980388321672577997)
                ·
                  refine ⟨102340117645620627216749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272906980388321672577997 102340117645620627216749)
                  ·
                    refine ⟨38377544117107735206281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102340117645620627216749 38377544117107735206281)
                    ·
                      rfl

theorem cell22_112110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_112110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112110 prefixEnd_112110 := by exact prefixLift 112110
  have htrace : WordTrace (prefixWord ++ tailWord_112110) baseStart_112110 baseEnd_112110 := by
    simpa [prefixWord, tailWord_112110, baseEnd_112110] using wordTrace_append hprefix tailTrace_112110
  have hstable : (prefixWord ++ tailWord_112110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112110).length < 2 ^ (prefixWord ++ tailWord_112110).sum := by decide
  have hdescent : baseEnd_112110 < baseStart_112110 := by decide
  rcases family_descends (prefixWord ++ tailWord_112110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112170 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_112170 : Nat := 118140960795 + 112170 * 2 ^ 59
def prefixEnd_112170 : Nat := 4983230072969 + 3 ^ 40 * 112170 * 2
def baseEnd_112170 : Nat := 38398083343287578706097

theorem tailTrace_112170 : CollatzResearch.WordTrace tailWord_112170 prefixEnd_112170 38398083343287578706097 := by
  unfold tailWord_112170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022794000908680488983491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2727450669089814637289309 1022794000908680488983491)
  ·
    refine ⟨1534191001363020733475237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1022794000908680488983491 1534191001363020733475237)
    ·
      refine ⟨287660812755566387526607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1534191001363020733475237 287660812755566387526607)
      ·
        refine ⟨431491219133349581289911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287660812755566387526607 431491219133349581289911)
        ·
          refine ⟨647236828700024371934867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431491219133349581289911 647236828700024371934867)
          ·
            refine ⟨970855243050036557902301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647236828700024371934867 970855243050036557902301)
            ·
              refine ⟨364070716143763709213363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 970855243050036557902301 364070716143763709213363)
              ·
                refine ⟨546106074215645563820045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364070716143763709213363 546106074215645563820045)
                ·
                  refine ⟨204789777830867086432517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 546106074215645563820045 204789777830867086432517)
                  ·
                    refine ⟨38398083343287578706097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204789777830867086432517 38398083343287578706097)
                    ·
                      rfl

theorem cell22_112170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_112170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112170 prefixEnd_112170 := by exact prefixLift 112170
  have htrace : WordTrace (prefixWord ++ tailWord_112170) baseStart_112170 baseEnd_112170 := by
    simpa [prefixWord, tailWord_112170, baseEnd_112170] using wordTrace_append hprefix tailTrace_112170
  have hstable : (prefixWord ++ tailWord_112170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112170).length < 2 ^ (prefixWord ++ tailWord_112170).sum := by decide
  have hdescent : baseEnd_112170 < baseStart_112170 := by decide
  rcases family_descends (prefixWord ++ tailWord_112170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112183 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 3, 5]
def baseStart_112183 : Nat := 118140960795 + 112183 * 2 ^ 59
def prefixEnd_112183 : Nat := 4983230072969 + 3 ^ 40 * 112183 * 2
def baseEnd_112183 : Nat := 38402533508959878131057

theorem tailTrace_112183 : CollatzResearch.WordTrace tailWord_112183 prefixEnd_112183 38402533508959878131057 := by
  unfold tailWord_112183
  simp only [CollatzResearch.WordTrace]
  refine ⟨4091650152587625176157203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2727766768391750117438135 4091650152587625176157203)
  ·
    refine ⟨6137475228881437764235805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4091650152587625176157203 6137475228881437764235805)
    ·
      refine ⟨2301553210830539161588427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6137475228881437764235805 2301553210830539161588427)
      ·
        refine ⟨3452329816245808742382641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2301553210830539161588427 3452329816245808742382641)
        ·
          refine ⟨2589247362184356556786981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3452329816245808742382641 2589247362184356556786981)
          ·
            refine ⟨485483880409566854397559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2589247362184356556786981 485483880409566854397559)
            ·
              refine ⟨728225820614350281596339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485483880409566854397559 728225820614350281596339)
              ·
                refine ⟨1092338730921525422394509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728225820614350281596339 1092338730921525422394509)
                ·
                  refine ⟨409627024095572033397941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1092338730921525422394509 409627024095572033397941)
                  ·
                    refine ⟨38402533508959878131057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 409627024095572033397941 38402533508959878131057)
                    ·
                      rfl

theorem cell22_112183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_112183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112183 prefixEnd_112183 := by exact prefixLift 112183
  have htrace : WordTrace (prefixWord ++ tailWord_112183) baseStart_112183 baseEnd_112183 := by
    simpa [prefixWord, tailWord_112183, baseEnd_112183] using wordTrace_append hprefix tailTrace_112183
  have hstable : (prefixWord ++ tailWord_112183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112183).length < 2 ^ (prefixWord ++ tailWord_112183).sum := by decide
  have hdescent : baseEnd_112183 < baseStart_112183 := by decide
  rcases family_descends (prefixWord ++ tailWord_112183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112232 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 2, 4]
def baseStart_112232 : Nat := 118140960795 + 112232 * 2 ^ 59
def prefixEnd_112232 : Nat := 4983230072969 + 3 ^ 40 * 112232 * 2
def baseEnd_112232 : Nat := 38419307210340083655907

theorem tailTrace_112232 : CollatzResearch.WordTrace tailWord_112232 prefixEnd_112232 38419307210340083655907 := by
  unfold tailWord_112232
  simp only [CollatzResearch.WordTrace]
  refine ⟨2046718664705053272345475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2728958219606737696460633 2046718664705053272345475)
  ·
    refine ⟨3070077997057579908518213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2046718664705053272345475 3070077997057579908518213)
    ·
      refine ⟨575639624448296232847165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3070077997057579908518213 575639624448296232847165)
      ·
        refine ⟨215864859168111087317687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 575639624448296232847165 215864859168111087317687)
        ·
          refine ⟨323797288752166630976531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215864859168111087317687 323797288752166630976531)
          ·
            refine ⟨485695933128249946464797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323797288752166630976531 485695933128249946464797)
            ·
              refine ⟨182135974923093729924299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485695933128249946464797 182135974923093729924299)
              ·
                refine ⟨273203962384640594886449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182135974923093729924299 273203962384640594886449)
                ·
                  refine ⟨204902971788480446164837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273203962384640594886449 204902971788480446164837)
                  ·
                    refine ⟨38419307210340083655907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204902971788480446164837 38419307210340083655907)
                    ·
                      rfl

theorem cell22_112232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_112232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112232 prefixEnd_112232 := by exact prefixLift 112232
  have htrace : WordTrace (prefixWord ++ tailWord_112232) baseStart_112232 baseEnd_112232 := by
    simpa [prefixWord, tailWord_112232, baseEnd_112232] using wordTrace_append hprefix tailTrace_112232
  have hstable : (prefixWord ++ tailWord_112232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112232).length < 2 ^ (prefixWord ++ tailWord_112232).sum := by decide
  have hdescent : baseEnd_112232 < baseStart_112232 := by decide
  rcases family_descends (prefixWord ++ tailWord_112232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112273 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 1, 7]
def baseStart_112273 : Nat := 118140960795 + 112273 * 2 ^ 59
def prefixEnd_112273 : Nat := 4983230072969 + 3 ^ 40 * 112273 * 2
def baseEnd_112273 : Nat := 38433342348229643380781

theorem tailTrace_112273 : CollatzResearch.WordTrace tailWord_112273 prefixEnd_112273 38433342348229643380781 := by
  unfold tailWord_112273
  simp only [CollatzResearch.WordTrace]
  refine ⟨4094932722261570546933473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2729955148174380364622315 4094932722261570546933473)
  ·
    refine ⟨3071199541696177910200105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4094932722261570546933473 3071199541696177910200105)
    ·
      refine ⟨2303399656272133432650079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3071199541696177910200105 2303399656272133432650079)
      ·
        refine ⟨3455099484408200148975119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2303399656272133432650079 3455099484408200148975119)
        ·
          refine ⟨5182649226612300223462679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3455099484408200148975119 5182649226612300223462679)
          ·
            refine ⟨7773973839918450335194019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5182649226612300223462679 7773973839918450335194019)
            ·
              refine ⟨11660960759877675502791029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7773973839918450335194019 11660960759877675502791029)
              ·
                refine ⟨1093215071238532078386659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11660960759877675502791029 1093215071238532078386659)
                ·
                  refine ⟨1639822606857798117579989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1093215071238532078386659 1639822606857798117579989)
                  ·
                    refine ⟨38433342348229643380781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1639822606857798117579989 38433342348229643380781)
                    ·
                      rfl

theorem cell22_112273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_112273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112273 prefixEnd_112273 := by exact prefixLift 112273
  have htrace : WordTrace (prefixWord ++ tailWord_112273) baseStart_112273 baseEnd_112273 := by
    simpa [prefixWord, tailWord_112273, baseEnd_112273] using wordTrace_append hprefix tailTrace_112273
  have hstable : (prefixWord ++ tailWord_112273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112273).length < 2 ^ (prefixWord ++ tailWord_112273).sum := by decide
  have hdescent : baseEnd_112273 < baseStart_112273 := by decide
  rcases family_descends (prefixWord ++ tailWord_112273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112326 : List Nat := [6, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_112326 : Nat := 118140960795 + 112326 * 2 ^ 59
def prefixEnd_112326 : Nat := 4983230072969 + 3 ^ 40 * 112326 * 2
def baseEnd_112326 : Nat := 12817161777118390601873

theorem tailTrace_112326 : CollatzResearch.WordTrace tailWord_112326 prefixEnd_112326 12817161777118390601873 := by
  unfold tailWord_112326
  simp only [CollatzResearch.WordTrace]
  refine ⟨128027055970923768706651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2731243860713040399075221 128027055970923768706651)
  ·
    refine ⟨192040583956385653059977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128027055970923768706651 192040583956385653059977)
    ·
      refine ⟨144030437967289239794983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192040583956385653059977 144030437967289239794983)
      ·
        refine ⟨216045656950933859692475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144030437967289239794983 216045656950933859692475)
        ·
          refine ⟨324068485426400789538713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216045656950933859692475 324068485426400789538713)
          ·
            refine ⟨243051364069800592154035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324068485426400789538713 243051364069800592154035)
            ·
              refine ⟨364577046104700888231053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243051364069800592154035 364577046104700888231053)
              ·
                refine ⟨136716392289262833086645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364577046104700888231053 136716392289262833086645)
                ·
                  refine ⟨12817161777118390601873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136716392289262833086645 12817161777118390601873)
                  ·
                    rfl

theorem cell22_112326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_112326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112326 prefixEnd_112326 := by exact prefixLift 112326
  have htrace : WordTrace (prefixWord ++ tailWord_112326) baseStart_112326 baseEnd_112326 := by
    simpa [prefixWord, tailWord_112326, baseEnd_112326] using wordTrace_append hprefix tailTrace_112326
  have hstable : (prefixWord ++ tailWord_112326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112326).length < 2 ^ (prefixWord ++ tailWord_112326).sum := by decide
  have hdescent : baseEnd_112326 < baseStart_112326 := by decide
  rcases family_descends (prefixWord ++ tailWord_112326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112365 : List Nat := [1, 5, 1, 2, 1, 12]
def baseStart_112365 : Nat := 118140960795 + 112365 * 2 ^ 59
def prefixEnd_112365 : Nat := 4983230072969 + 3 ^ 40 * 112365 * 2
def baseEnd_112365 : Nat := 474874516399655186179

theorem tailTrace_112365 : CollatzResearch.WordTrace tailWord_112365 prefixEnd_112365 474874516399655186179 := by
  unfold tailWord_112365
  simp only [CollatzResearch.WordTrace]
  refine ⟨4098288237928270259282549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2732192158618846839521699 4098288237928270259282549)
  ·
    refine ⟨384214522305775336807739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4098288237928270259282549 384214522305775336807739)
    ·
      refine ⟨576321783458663005211609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384214522305775336807739 576321783458663005211609)
      ·
        refine ⟨432241337593997253908707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 576321783458663005211609 432241337593997253908707)
        ·
          refine ⟨648362006390995880863061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432241337593997253908707 648362006390995880863061)
          ·
            refine ⟨474874516399655186179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 648362006390995880863061 474874516399655186179)
            ·
              rfl

theorem cell22_112365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 12].length) (baseStart_112365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112365 prefixEnd_112365 := by exact prefixLift 112365
  have htrace : WordTrace (prefixWord ++ tailWord_112365) baseStart_112365 baseEnd_112365 := by
    simpa [prefixWord, tailWord_112365, baseEnd_112365] using wordTrace_append hprefix tailTrace_112365
  have hstable : (prefixWord ++ tailWord_112365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112365).length < 2 ^ (prefixWord ++ tailWord_112365).sum := by decide
  have hdescent : baseEnd_112365 < baseStart_112365 := by decide
  rcases family_descends (prefixWord ++ tailWord_112365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112369 : List Nat := [1, 2, 2, 2, 2, 4, 2, 2, 2, 3]
def baseStart_112369 : Nat := 118140960795 + 112369 * 2 ^ 59
def prefixEnd_112369 : Nat := 4983230072969 + 3 ^ 40 * 112369 * 2
def baseEnd_112369 : Nat := 38466205110117392980487

theorem tailTrace_112369 : CollatzResearch.WordTrace tailWord_112369 prefixEnd_112369 38466205110117392980487 := by
  unfold tailWord_112369
  simp only [CollatzResearch.WordTrace]
  refine ⟨4098434129913778942428161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2732289419942519294952107 4098434129913778942428161)
  ·
    refine ⟨3073825597435334206821121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4098434129913778942428161 3073825597435334206821121)
    ·
      refine ⟨2305369198076500655115841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3073825597435334206821121 2305369198076500655115841)
      ·
        refine ⟨1729026898557375491336881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2305369198076500655115841 1729026898557375491336881)
        ·
          refine ⟨1296770173918031618502661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1729026898557375491336881 1296770173918031618502661)
          ·
            refine ⟨243144407609630928469249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1296770173918031618502661 243144407609630928469249)
            ·
              refine ⟨182358305707223196351937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243144407609630928469249 182358305707223196351937)
              ·
                refine ⟨136768729280417397263953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182358305707223196351937 136768729280417397263953)
                ·
                  refine ⟨102576546960313047947965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136768729280417397263953 102576546960313047947965)
                  ·
                    refine ⟨38466205110117392980487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102576546960313047947965 38466205110117392980487)
                    ·
                      rfl

theorem cell22_112369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_112369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112369 prefixEnd_112369 := by exact prefixLift 112369
  have htrace : WordTrace (prefixWord ++ tailWord_112369) baseStart_112369 baseEnd_112369 := by
    simpa [prefixWord, tailWord_112369, baseEnd_112369] using wordTrace_append hprefix tailTrace_112369
  have hstable : (prefixWord ++ tailWord_112369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112369).length < 2 ^ (prefixWord ++ tailWord_112369).sum := by decide
  have hdescent : baseEnd_112369 < baseStart_112369 := by decide
  rcases family_descends (prefixWord ++ tailWord_112369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112442 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_112442 : Nat := 118140960795 + 112442 * 2 ^ 59
def prefixEnd_112442 : Nat := 4983230072969 + 3 ^ 40 * 112442 * 2
def baseEnd_112442 : Nat := 38491194501969535905263

theorem tailTrace_112442 : CollatzResearch.WordTrace tailWord_112442 prefixEnd_112442 38491194501969535905263 := by
  unfold tailWord_112442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025274164662328102458895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2734064439099541606557053 1025274164662328102458895)
  ·
    refine ⟨1537911246993492153688343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1025274164662328102458895 1537911246993492153688343)
    ·
      refine ⟨2306866870490238230532515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537911246993492153688343 2306866870490238230532515)
      ·
        refine ⟨3460300305735357345798773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2306866870490238230532515 3460300305735357345798773)
        ·
          refine ⟨324403153662689751168635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3460300305735357345798773 324403153662689751168635)
          ·
            refine ⟨486604730494034626752953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324403153662689751168635 486604730494034626752953)
            ·
              refine ⟨364953547870525970064715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 486604730494034626752953 364953547870525970064715)
              ·
                refine ⟨547430321805788955097073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364953547870525970064715 547430321805788955097073)
                ·
                  refine ⟨410572741354341716322805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 547430321805788955097073 410572741354341716322805)
                  ·
                    refine ⟨38491194501969535905263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 410572741354341716322805 38491194501969535905263)
                    ·
                      rfl

theorem cell22_112442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_112442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112442 prefixEnd_112442 := by exact prefixLift 112442
  have htrace : WordTrace (prefixWord ++ tailWord_112442) baseStart_112442 baseEnd_112442 := by
    simpa [prefixWord, tailWord_112442, baseEnd_112442] using wordTrace_append hprefix tailTrace_112442
  have hstable : (prefixWord ++ tailWord_112442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112442).length < 2 ^ (prefixWord ++ tailWord_112442).sum := by decide
  have hdescent : baseEnd_112442 < baseStart_112442 := by decide
  rcases family_descends (prefixWord ++ tailWord_112442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112667 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 2, 7]
def baseStart_112667 : Nat := 118140960795 + 112667 * 2 ^ 59
def prefixEnd_112667 : Nat := 4983230072969 + 3 ^ 40 * 112667 * 2
def baseEnd_112667 : Nat := 38568216600143949029573

theorem tailTrace_112667 : CollatzResearch.WordTrace tailWord_112667 prefixEnd_112667 38568216600143949029573 := by
  unfold tailWord_112667
  simp only [CollatzResearch.WordTrace]
  refine ⟨4109303082834175836776255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2739535388556117224517503 4109303082834175836776255)
  ·
    refine ⟨6163954624251263755164383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4109303082834175836776255 6163954624251263755164383)
    ·
      refine ⟨9245931936376895632746575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6163954624251263755164383 9245931936376895632746575)
      ·
        refine ⟨13868897904565343449119863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9245931936376895632746575 13868897904565343449119863)
        ·
          refine ⟨20803346856848015173679795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13868897904565343449119863 20803346856848015173679795)
          ·
            refine ⟨31205020285272022760519693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20803346856848015173679795 31205020285272022760519693)
            ·
              refine ⟨11701882606977008535194885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31205020285272022760519693 11701882606977008535194885)
              ·
                refine ⟨2194102988808189100349041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11701882606977008535194885 2194102988808189100349041)
                ·
                  refine ⟨1645577241606141825261781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2194102988808189100349041 1645577241606141825261781)
                  ·
                    refine ⟨38568216600143949029573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1645577241606141825261781 38568216600143949029573)
                    ·
                      rfl

theorem cell22_112667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 7].length) (baseStart_112667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112667 prefixEnd_112667 := by exact prefixLift 112667
  have htrace : WordTrace (prefixWord ++ tailWord_112667) baseStart_112667 baseEnd_112667 := by
    simpa [prefixWord, tailWord_112667, baseEnd_112667] using wordTrace_append hprefix tailTrace_112667
  have hstable : (prefixWord ++ tailWord_112667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112667).length < 2 ^ (prefixWord ++ tailWord_112667).sum := by decide
  have hdescent : baseEnd_112667 < baseStart_112667 := by decide
  rcases family_descends (prefixWord ++ tailWord_112667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112669 : List Nat := [1, 4, 2, 2, 2, 1, 1, 9]
def baseStart_112669 : Nat := 118140960795 + 112669 * 2 ^ 59
def prefixEnd_112669 : Nat := 4983230072969 + 3 ^ 40 * 112669 * 2
def baseEnd_112669 : Nat := 4285433471224067831063

theorem tailTrace_112669 : CollatzResearch.WordTrace tailWord_112669 prefixEnd_112669 4285433471224067831063 := by
  unfold tailWord_112669
  simp only [CollatzResearch.WordTrace]
  refine ⟨4109376028826930178349061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2739584019217953452232707 4109376028826930178349061)
  ·
    refine ⟨770508005405049408440449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4109376028826930178349061 770508005405049408440449)
    ·
      refine ⟨577881004053787056330337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 770508005405049408440449 577881004053787056330337)
      ·
        refine ⟨433410753040340292247753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 577881004053787056330337 433410753040340292247753)
        ·
          refine ⟨325058064780255219185815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433410753040340292247753 325058064780255219185815)
          ·
            refine ⟨487587097170382828778723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325058064780255219185815 487587097170382828778723)
            ·
              refine ⟨731380645755574243168085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487587097170382828778723 731380645755574243168085)
              ·
                refine ⟨4285433471224067831063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 731380645755574243168085 4285433471224067831063)
                ·
                  rfl

theorem cell22_112669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 9].length) (baseStart_112669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112669 prefixEnd_112669 := by exact prefixLift 112669
  have htrace : WordTrace (prefixWord ++ tailWord_112669) baseStart_112669 baseEnd_112669 := by
    simpa [prefixWord, tailWord_112669, baseEnd_112669] using wordTrace_append hprefix tailTrace_112669
  have hstable : (prefixWord ++ tailWord_112669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112669).length < 2 ^ (prefixWord ++ tailWord_112669).sum := by decide
  have hdescent : baseEnd_112669 < baseStart_112669 := by decide
  rcases family_descends (prefixWord ++ tailWord_112669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112673 : List Nat := [1, 2, 3, 2, 4, 1, 1, 3, 2, 3]
def baseStart_112673 : Nat := 118140960795 + 112673 * 2 ^ 59
def prefixEnd_112673 : Nat := 4983230072969 + 3 ^ 40 * 112673 * 2
def baseEnd_112673 : Nat := 38570270522761933379555

theorem tailTrace_112673 : CollatzResearch.WordTrace tailWord_112673 prefixEnd_112673 38570270522761933379555 := by
  unfold tailWord_112673
  simp only [CollatzResearch.WordTrace]
  refine ⟨4109521920812438861494673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2739681280541625907663115 4109521920812438861494673)
  ·
    refine ⟨3082141440609329146121005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4109521920812438861494673 3082141440609329146121005)
    ·
      refine ⟨1155803040228498429795377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3082141440609329146121005 1155803040228498429795377)
      ·
        refine ⟨866852280171373822346533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1155803040228498429795377 866852280171373822346533)
        ·
          refine ⟨162534802532132591689975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 866852280171373822346533 162534802532132591689975)
          ·
            refine ⟨243802203798198887534963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162534802532132591689975 243802203798198887534963)
            ·
              refine ⟨365703305697298331302445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243802203798198887534963 365703305697298331302445)
              ·
                refine ⟨137138739636486874238417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365703305697298331302445 137138739636486874238417)
                ·
                  refine ⟨102854054727365155678813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137138739636486874238417 102854054727365155678813)
                  ·
                    refine ⟨38570270522761933379555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102854054727365155678813 38570270522761933379555)
                    ·
                      rfl

theorem cell22_112673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_112673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112673 prefixEnd_112673 := by exact prefixLift 112673
  have htrace : WordTrace (prefixWord ++ tailWord_112673) baseStart_112673 baseEnd_112673 := by
    simpa [prefixWord, tailWord_112673, baseEnd_112673] using wordTrace_append hprefix tailTrace_112673
  have hstable : (prefixWord ++ tailWord_112673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112673).length < 2 ^ (prefixWord ++ tailWord_112673).sum := by decide
  have hdescent : baseEnd_112673 < baseStart_112673 := by decide
  rcases family_descends (prefixWord ++ tailWord_112673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112729 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 2, 5]
def baseStart_112729 : Nat := 118140960795 + 112729 * 2 ^ 59
def prefixEnd_112729 : Nat := 4983230072969 + 3 ^ 40 * 112729 * 2
def baseEnd_112729 : Nat := 38589440467196453979383

theorem tailTrace_112729 : CollatzResearch.WordTrace tailWord_112729 prefixEnd_112729 38589440467196453979383 := by
  unfold tailWord_112729
  simp only [CollatzResearch.WordTrace]
  refine ⟨4111564408609560425533241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2741042939073040283688827 4111564408609560425533241)
  ·
    refine ⟨3083673306457170319149931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4111564408609560425533241 3083673306457170319149931)
    ·
      refine ⟨4625509959685755478724897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3083673306457170319149931 4625509959685755478724897)
      ·
        refine ⟨3469132469764316609043673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4625509959685755478724897 3469132469764316609043673)
        ·
          refine ⟨2601849352323237456782755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3469132469764316609043673 2601849352323237456782755)
          ·
            refine ⟨3902774028484856185174133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2601849352323237456782755 3902774028484856185174133)
            ·
              refine ⟨365885065170455267360075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3902774028484856185174133 365885065170455267360075)
              ·
                refine ⟨548827597755682901040113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365885065170455267360075 548827597755682901040113)
                ·
                  refine ⟨411620698316762175780085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 548827597755682901040113 411620698316762175780085)
                  ·
                    refine ⟨38589440467196453979383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 411620698316762175780085 38589440467196453979383)
                    ·
                      rfl

theorem cell22_112729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_112729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112729 prefixEnd_112729 := by exact prefixLift 112729
  have htrace : WordTrace (prefixWord ++ tailWord_112729) baseStart_112729 baseEnd_112729 := by
    simpa [prefixWord, tailWord_112729, baseEnd_112729] using wordTrace_append hprefix tailTrace_112729
  have hstable : (prefixWord ++ tailWord_112729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112729).length < 2 ^ (prefixWord ++ tailWord_112729).sum := by decide
  have hdescent : baseEnd_112729 < baseStart_112729 := by decide
  rcases family_descends (prefixWord ++ tailWord_112729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112776 : List Nat := [2, 1, 3, 4, 1, 1, 1, 3, 6]
def baseStart_112776 : Nat := 118140960795 + 112776 * 2 ^ 59
def prefixEnd_112776 : Nat := 4983230072969 + 3 ^ 40 * 112776 * 2
def baseEnd_112776 : Nat := 12868509842567999351413

theorem tailTrace_112776 : CollatzResearch.WordTrace tailWord_112776 prefixEnd_112776 12868509842567999351413 := by
  unfold tailWord_112776
  simp only [CollatzResearch.WordTrace]
  refine ⟨2056639319719643726247091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2742185759626191634996121 2056639319719643726247091)
  ·
    refine ⟨3084958979579465589370637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2056639319719643726247091 3084958979579465589370637)
    ·
      refine ⟨1156859617342299596013989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3084958979579465589370637 1156859617342299596013989)
      ·
        refine ⟨216911178251681174252623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1156859617342299596013989 216911178251681174252623)
        ·
          refine ⟨325366767377521761378935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216911178251681174252623 325366767377521761378935)
          ·
            refine ⟨488050151066282642068403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325366767377521761378935 488050151066282642068403)
            ·
              refine ⟨732075226599423963102605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488050151066282642068403 732075226599423963102605)
              ·
                refine ⟨274528209974783986163477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 732075226599423963102605 274528209974783986163477)
                ·
                  refine ⟨12868509842567999351413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 274528209974783986163477 12868509842567999351413)
                  ·
                    rfl

theorem cell22_112776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_112776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112776 prefixEnd_112776 := by exact prefixLift 112776
  have htrace : WordTrace (prefixWord ++ tailWord_112776) baseStart_112776 baseEnd_112776 := by
    simpa [prefixWord, tailWord_112776, baseEnd_112776] using wordTrace_append hprefix tailTrace_112776
  have hstable : (prefixWord ++ tailWord_112776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112776).length < 2 ^ (prefixWord ++ tailWord_112776).sum := by decide
  have hdescent : baseEnd_112776 < baseStart_112776 := by decide
  rcases family_descends (prefixWord ++ tailWord_112776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112789 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_112789 : Nat := 118140960795 + 112789 * 2 ^ 59
def prefixEnd_112789 : Nat := 4983230072969 + 3 ^ 40 * 112789 * 2
def baseEnd_112789 : Nat := 38609979693376297479199

theorem tailTrace_112789 : CollatzResearch.WordTrace tailWord_112789 prefixEnd_112789 38609979693376297479199 := by
  unfold tailWord_112789
  simp only [CollatzResearch.WordTrace]
  refine ⟨4113752788392190672717421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2742501858928127115144947 4113752788392190672717421)
  ·
    refine ⟨1542657295647071502269033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4113752788392190672717421 1542657295647071502269033)
    ·
      refine ⟨1156992971735303626701775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1542657295647071502269033 1156992971735303626701775)
      ·
        refine ⟨1735489457602955440052663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156992971735303626701775 1735489457602955440052663)
        ·
          refine ⟨2603234186404433160078995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735489457602955440052663 2603234186404433160078995)
          ·
            refine ⟨3904851279606649740118493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2603234186404433160078995 3904851279606649740118493)
            ·
              refine ⟨1464319229852493652544435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3904851279606649740118493 1464319229852493652544435)
              ·
                refine ⟨2196478844778740478816653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1464319229852493652544435 2196478844778740478816653)
                ·
                  refine ⟨823679566792027679556245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2196478844778740478816653 823679566792027679556245)
                  ·
                    refine ⟨38609979693376297479199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 823679566792027679556245 38609979693376297479199)
                    ·
                      rfl

theorem cell22_112789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_112789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112789 prefixEnd_112789 := by exact prefixLift 112789
  have htrace : WordTrace (prefixWord ++ tailWord_112789) baseStart_112789 baseEnd_112789 := by
    simpa [prefixWord, tailWord_112789, baseEnd_112789] using wordTrace_append hprefix tailTrace_112789
  have hstable : (prefixWord ++ tailWord_112789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112789).length < 2 ^ (prefixWord ++ tailWord_112789).sum := by decide
  have hdescent : baseEnd_112789 < baseStart_112789 := by decide
  rcases family_descends (prefixWord ++ tailWord_112789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112896 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 3, 4]
def baseStart_112896 : Nat := 118140960795 + 112896 * 2 ^ 59
def prefixEnd_112896 : Nat := 4983230072969 + 3 ^ 40 * 112896 * 2
def baseEnd_112896 : Nat := 38646607980063685053871

theorem tailTrace_112896 : CollatzResearch.WordTrace tailWord_112896 prefixEnd_112896 38646607980063685053871 := by
  unfold tailWord_112896
  simp only [CollatzResearch.WordTrace]
  refine ⟨2058827699502273973431271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2745103599336365297908361 2058827699502273973431271)
  ·
    refine ⟨3088241549253410960146907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2058827699502273973431271 3088241549253410960146907)
    ·
      refine ⟨4632362323880116440220361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3088241549253410960146907 4632362323880116440220361)
      ·
        refine ⟨3474271742910087330165271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4632362323880116440220361 3474271742910087330165271)
        ·
          refine ⟨5211407614365130995247907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3474271742910087330165271 5211407614365130995247907)
          ·
            refine ⟨7817111421547696492871861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5211407614365130995247907 7817111421547696492871861)
            ·
              refine ⟨732854195770096546206737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7817111421547696492871861 732854195770096546206737)
              ·
                refine ⟨549640646827572409655053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 732854195770096546206737 549640646827572409655053)
                ·
                  refine ⟨206115242560339653620645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 549640646827572409655053 206115242560339653620645)
                  ·
                    refine ⟨38646607980063685053871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 206115242560339653620645 38646607980063685053871)
                    ·
                      rfl

theorem cell22_112896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_112896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112896 prefixEnd_112896 := by exact prefixLift 112896
  have htrace : WordTrace (prefixWord ++ tailWord_112896) baseStart_112896 baseEnd_112896 := by
    simpa [prefixWord, tailWord_112896, baseEnd_112896] using wordTrace_append hprefix tailTrace_112896
  have hstable : (prefixWord ++ tailWord_112896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112896).length < 2 ^ (prefixWord ++ tailWord_112896).sum := by decide
  have hdescent : baseEnd_112896 < baseStart_112896 := by decide
  rcases family_descends (prefixWord ++ tailWord_112896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112898 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_112898 : Nat := 118140960795 + 112898 * 2 ^ 59
def prefixEnd_112898 : Nat := 4983230072969 + 3 ^ 40 * 112898 * 2
def baseEnd_112898 : Nat := 38647292620936346503865

theorem tailTrace_112898 : CollatzResearch.WordTrace tailWord_112898 prefixEnd_112898 38647292620936346503865 := by
  unfold tailWord_112898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1029432086249325572108837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2745152229998201525623565 1029432086249325572108837)
  ·
    refine ⟨193018516171748544770407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1029432086249325572108837 193018516171748544770407)
    ·
      refine ⟨289527774257622817155611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193018516171748544770407 289527774257622817155611)
      ·
        refine ⟨434291661386434225733417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289527774257622817155611 434291661386434225733417)
        ·
          refine ⟨325718746039825669300063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434291661386434225733417 325718746039825669300063)
          ·
            refine ⟨488578119059738503950095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325718746039825669300063 488578119059738503950095)
            ·
              refine ⟨732867178589607755925143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488578119059738503950095 732867178589607755925143)
              ·
                refine ⟨1099300767884411633887715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732867178589607755925143 1099300767884411633887715)
                ·
                  refine ⟨1648951151826617450831573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1099300767884411633887715 1648951151826617450831573)
                  ·
                    refine ⟨38647292620936346503865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1648951151826617450831573 38647292620936346503865)
                    ·
                      rfl

theorem cell22_112898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_112898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112898 prefixEnd_112898 := by exact prefixLift 112898
  have htrace : WordTrace (prefixWord ++ tailWord_112898) baseStart_112898 baseEnd_112898 := by
    simpa [prefixWord, tailWord_112898, baseEnd_112898] using wordTrace_append hprefix tailTrace_112898
  have hstable : (prefixWord ++ tailWord_112898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112898).length < 2 ^ (prefixWord ++ tailWord_112898).sum := by decide
  have hdescent : baseEnd_112898 < baseStart_112898 := by decide
  rcases family_descends (prefixWord ++ tailWord_112898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112930 : List Nat := [3, 3, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_112930 : Nat := 118140960795 + 112930 * 2 ^ 59
def prefixEnd_112930 : Nat := 4983230072969 + 3 ^ 40 * 112930 * 2
def baseEnd_112930 : Nat := 38658246874898929703767

theorem tailTrace_112930 : CollatzResearch.WordTrace tailWord_112930 prefixEnd_112930 38658246874898929703767 := by
  unfold tailWord_112930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1029723870220342938400061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2745930320587581169066829 1029723870220342938400061)
  ·
    refine ⟨386146451332628601900023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1029723870220342938400061 386146451332628601900023)
    ·
      refine ⟨579219676998942902850035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386146451332628601900023 579219676998942902850035)
      ·
        refine ⟨868829515498414354275053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579219676998942902850035 868829515498414354275053)
        ·
          refine ⟨325811068311905382853145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 868829515498414354275053 325811068311905382853145)
          ·
            refine ⟨244358301233929037139859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325811068311905382853145 244358301233929037139859)
            ·
              refine ⟨366537451850893555709789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244358301233929037139859 366537451850893555709789)
              ·
                refine ⟨137451544444085083391171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366537451850893555709789 137451544444085083391171)
                ·
                  refine ⟨206177316666127625086757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137451544444085083391171 206177316666127625086757)
                  ·
                    refine ⟨38658246874898929703767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 206177316666127625086757 38658246874898929703767)
                    ·
                      rfl

theorem cell22_112930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_112930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112930 prefixEnd_112930 := by exact prefixLift 112930
  have htrace : WordTrace (prefixWord ++ tailWord_112930) baseStart_112930 baseEnd_112930 := by
    simpa [prefixWord, tailWord_112930, baseEnd_112930] using wordTrace_append hprefix tailTrace_112930
  have hstable : (prefixWord ++ tailWord_112930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112930).length < 2 ^ (prefixWord ++ tailWord_112930).sum := by decide
  have hdescent : baseEnd_112930 < baseStart_112930 := by decide
  rcases family_descends (prefixWord ++ tailWord_112930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112956 : List Nat := [2, 2, 2, 2, 1, 2, 2, 9]
def baseStart_112956 : Nat := 118140960795 + 112956 * 2 ^ 59
def prefixEnd_112956 : Nat := 4983230072969 + 3 ^ 40 * 112956 * 2
def baseEnd_112956 : Nat := 4296349689582614283743

theorem tailTrace_112956 : CollatzResearch.WordTrace tailWord_112956 prefixEnd_112956 4296349689582614283743 := by
  unfold tailWord_112956
  simp only [CollatzResearch.WordTrace]
  refine ⟨2059921889393589097023361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2746562519191452129364481 2059921889393589097023361)
  ·
    refine ⟨1544941417045191822767521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2059921889393589097023361 1544941417045191822767521)
    ·
      refine ⟨1158706062783893867075641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1544941417045191822767521 1158706062783893867075641)
      ·
        refine ⟨869029547087920400306731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1158706062783893867075641 869029547087920400306731)
        ·
          refine ⟨1303544320631880600460097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869029547087920400306731 1303544320631880600460097)
          ·
            refine ⟨977658240473910450345073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1303544320631880600460097 977658240473910450345073)
            ·
              refine ⟨733243680355432837758805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 977658240473910450345073 733243680355432837758805)
              ·
                refine ⟨4296349689582614283743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 733243680355432837758805 4296349689582614283743)
                ·
                  rfl

theorem cell22_112956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 9].length) (baseStart_112956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112956 prefixEnd_112956 := by exact prefixLift 112956
  have htrace : WordTrace (prefixWord ++ tailWord_112956) baseStart_112956 baseEnd_112956 := by
    simpa [prefixWord, tailWord_112956, baseEnd_112956] using wordTrace_append hprefix tailTrace_112956
  have hstable : (prefixWord ++ tailWord_112956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112956).length < 2 ^ (prefixWord ++ tailWord_112956).sum := by decide
  have hdescent : baseEnd_112956 < baseStart_112956 := by decide
  rcases family_descends (prefixWord ++ tailWord_112956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112958 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_112958 : Nat := 118140960795 + 112958 * 2 ^ 59
def prefixEnd_112958 : Nat := 4983230072969 + 3 ^ 40 * 112958 * 2
def baseEnd_112958 : Nat := 38667831847116190003681

theorem tailTrace_112958 : CollatzResearch.WordTrace tailWord_112958 prefixEnd_112958 38667831847116190003681 := by
  unfold tailWord_112958
  simp only [CollatzResearch.WordTrace]
  refine ⟨514989590597491566952441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2746611149853288357079685 514989590597491566952441)
  ·
    refine ⟨386242192948118675214331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 514989590597491566952441 386242192948118675214331)
    ·
      refine ⟨579363289422178012821497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386242192948118675214331 579363289422178012821497)
      ·
        refine ⟨434522467066633509616123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579363289422178012821497 434522467066633509616123)
        ·
          refine ⟨651783700599950264424185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434522467066633509616123 651783700599950264424185)
          ·
            refine ⟨488837775449962698318139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651783700599950264424185 488837775449962698318139)
            ·
              refine ⟨733256663174944047477209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488837775449962698318139 733256663174944047477209)
              ·
                refine ⟨549942497381208035607907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733256663174944047477209 549942497381208035607907)
                ·
                  refine ⟨824913746071812053411861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 549942497381208035607907 824913746071812053411861)
                  ·
                    refine ⟨38667831847116190003681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 824913746071812053411861 38667831847116190003681)
                    ·
                      rfl

theorem cell22_112958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_112958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112958 prefixEnd_112958 := by exact prefixLift 112958
  have htrace : WordTrace (prefixWord ++ tailWord_112958) baseStart_112958 baseEnd_112958 := by
    simpa [prefixWord, tailWord_112958, baseEnd_112958] using wordTrace_append hprefix tailTrace_112958
  have hstable : (prefixWord ++ tailWord_112958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112958).length < 2 ^ (prefixWord ++ tailWord_112958).sum := by decide
  have hdescent : baseEnd_112958 < baseStart_112958 := by decide
  rcases family_descends (prefixWord ++ tailWord_112958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112986 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_112986 : Nat := 118140960795 + 112986 * 2 ^ 59
def prefixEnd_112986 : Nat := 4983230072969 + 3 ^ 40 * 112986 * 2
def baseEnd_112986 : Nat := 38677416819333450303595

theorem tailTrace_112986 : CollatzResearch.WordTrace tailWord_112986 prefixEnd_112986 38677416819333450303595 := by
  unfold tailWord_112986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1030234492169623329409703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2747291979118995545092541 1030234492169623329409703)
  ·
    refine ⟨1545351738254434994114555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1030234492169623329409703 1545351738254434994114555)
    ·
      refine ⟨2318027607381652491171833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1545351738254434994114555 2318027607381652491171833)
      ·
        refine ⟨1738520705536239368378875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2318027607381652491171833 1738520705536239368378875)
        ·
          refine ⟨2607781058304359052568313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738520705536239368378875 2607781058304359052568313)
          ·
            refine ⟨1955835793728269289426235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2607781058304359052568313 1955835793728269289426235)
            ·
              refine ⟨2933753690592403934139353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1955835793728269289426235 2933753690592403934139353)
              ·
                refine ⟨2200315267944302950604515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2933753690592403934139353 2200315267944302950604515)
                ·
                  refine ⟨3300472901916454425906773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2200315267944302950604515 3300472901916454425906773)
                  ·
                    refine ⟨38677416819333450303595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3300472901916454425906773 38677416819333450303595)
                    ·
                      rfl

theorem cell22_112986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_112986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_112986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_112986 prefixEnd_112986 := by exact prefixLift 112986
  have htrace : WordTrace (prefixWord ++ tailWord_112986) baseStart_112986 baseEnd_112986 := by
    simpa [prefixWord, tailWord_112986, baseEnd_112986] using wordTrace_append hprefix tailTrace_112986
  have hstable : (prefixWord ++ tailWord_112986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112986).length < 2 ^ (prefixWord ++ tailWord_112986).sum := by decide
  have hdescent : baseEnd_112986 < baseStart_112986 := by decide
  rcases family_descends (prefixWord ++ tailWord_112986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113001 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 7]
def baseStart_113001 : Nat := 118140960795 + 113001 * 2 ^ 59
def prefixEnd_113001 : Nat := 4983230072969 + 3 ^ 40 * 113001 * 2
def baseEnd_113001 : Nat := 12894183875292803726183

theorem tailTrace_113001 : CollatzResearch.WordTrace tailWord_113001 prefixEnd_113001 12894183875292803726183 := by
  unfold tailWord_113001
  simp only [CollatzResearch.WordTrace]
  refine ⟨4121485063624150879434857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2747656709082767252956571 4121485063624150879434857)
  ·
    refine ⟨3091113797718113159576143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4121485063624150879434857 3091113797718113159576143)
    ·
      refine ⟨4636670696577169739364215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3091113797718113159576143 4636670696577169739364215)
      ·
        refine ⟨6955006044865754609046323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4636670696577169739364215 6955006044865754609046323)
        ·
          refine ⟨10432509067298631913569485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6955006044865754609046323 10432509067298631913569485)
          ·
            refine ⟨3912190900236986967588557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10432509067298631913569485 3912190900236986967588557)
            ·
              refine ⟨1467071587588870112845709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3912190900236986967588557 1467071587588870112845709)
              ·
                refine ⟨550151845345826292317141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1467071587588870112845709 550151845345826292317141)
                ·
                  refine ⟨12894183875292803726183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 550151845345826292317141 12894183875292803726183)
                  ·
                    rfl

theorem cell22_113001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_113001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113001 prefixEnd_113001 := by exact prefixLift 113001
  have htrace : WordTrace (prefixWord ++ tailWord_113001) baseStart_113001 baseEnd_113001 := by
    simpa [prefixWord, tailWord_113001, baseEnd_113001] using wordTrace_append hprefix tailTrace_113001
  have hstable : (prefixWord ++ tailWord_113001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113001).length < 2 ^ (prefixWord ++ tailWord_113001).sum := by decide
  have hdescent : baseEnd_113001 < baseStart_113001 := by decide
  rcases family_descends (prefixWord ++ tailWord_113001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113183 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 2, 8]
def baseStart_113183 : Nat := 118140960795 + 113183 * 2 ^ 59
def prefixEnd_113183 : Nat := 4983230072969 + 3 ^ 40 * 113183 * 2
def baseEnd_113183 : Nat := 38744853945290603127991

theorem tailTrace_113183 : CollatzResearch.WordTrace tailWord_113183 prefixEnd_113183 38744853945290603127991 := by
  unfold tailWord_113183
  simp only [CollatzResearch.WordTrace]
  refine ⟨4128123148964795962560203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2752082099309863975040135 4128123148964795962560203)
  ·
    refine ⟨6192184723447193943840305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4128123148964795962560203 6192184723447193943840305)
    ·
      refine ⟨4644138542585395457880229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6192184723447193943840305 4644138542585395457880229)
      ·
        refine ⟨870775976734761648352543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4644138542585395457880229 870775976734761648352543)
        ·
          refine ⟨1306163965102142472528815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 870775976734761648352543 1306163965102142472528815)
          ·
            refine ⟨1959245947653213708793223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306163965102142472528815 1959245947653213708793223)
            ·
              refine ⟨2938868921479820563189835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1959245947653213708793223 2938868921479820563189835)
              ·
                refine ⟨4408303382219730844784753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2938868921479820563189835 4408303382219730844784753)
                ·
                  refine ⟨3306227536664798133588565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4408303382219730844784753 3306227536664798133588565)
                  ·
                    refine ⟨38744853945290603127991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3306227536664798133588565 38744853945290603127991)
                    ·
                      rfl

theorem cell22_113183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_113183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113183 prefixEnd_113183 := by exact prefixLift 113183
  have htrace : WordTrace (prefixWord ++ tailWord_113183) baseStart_113183 baseEnd_113183 := by
    simpa [prefixWord, tailWord_113183, baseEnd_113183] using wordTrace_append hprefix tailTrace_113183
  have hstable : (prefixWord ++ tailWord_113183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113183).length < 2 ^ (prefixWord ++ tailWord_113183).sum := by decide
  have hdescent : baseEnd_113183 < baseStart_113183 := by decide
  rcases family_descends (prefixWord ++ tailWord_113183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113187 : List Nat := [1, 1, 1, 4, 4, 1, 4, 1, 5]
def baseStart_113187 : Nat := 118140960795 + 113187 * 2 ^ 59
def prefixEnd_113187 : Nat := 4983230072969 + 3 ^ 40 * 113187 * 2
def baseEnd_113187 : Nat := 12915407742345308675993

theorem tailTrace_113187 : CollatzResearch.WordTrace tailWord_113187 prefixEnd_113187 12915407742345308675993 := by
  unfold tailWord_113187
  simp only [CollatzResearch.WordTrace]
  refine ⟨4128269040950304645705815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2752179360633536430470543 4128269040950304645705815)
  ·
    refine ⟨6192403561425456968558723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4128269040950304645705815 6192403561425456968558723)
    ·
      refine ⟨9288605342138185452838085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6192403561425456968558723 9288605342138185452838085)
      ·
        refine ⟨1741613501650909772407141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9288605342138185452838085 1741613501650909772407141)
        ·
          refine ⟨326552531559545582326339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1741613501650909772407141 326552531559545582326339)
          ·
            refine ⟨489828797339318373489509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326552531559545582326339 489828797339318373489509)
            ·
              refine ⟨91842899501122195029283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 489828797339318373489509 91842899501122195029283)
              ·
                refine ⟨137764349251683292543925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91842899501122195029283 137764349251683292543925)
                ·
                  refine ⟨12915407742345308675993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137764349251683292543925 12915407742345308675993)
                  ·
                    rfl

theorem cell22_113187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 1, 5].length) (baseStart_113187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113187 prefixEnd_113187 := by exact prefixLift 113187
  have htrace : WordTrace (prefixWord ++ tailWord_113187) baseStart_113187 baseEnd_113187 := by
    simpa [prefixWord, tailWord_113187, baseEnd_113187] using wordTrace_append hprefix tailTrace_113187
  have hstable : (prefixWord ++ tailWord_113187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113187).length < 2 ^ (prefixWord ++ tailWord_113187).sum := by decide
  have hdescent : baseEnd_113187 < baseStart_113187 := by decide
  rcases family_descends (prefixWord ++ tailWord_113187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113262 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_113262 : Nat := 118140960795 + 113262 * 2 ^ 59
def prefixEnd_113262 : Nat := 4983230072969 + 3 ^ 40 * 113262 * 2
def baseEnd_113262 : Nat := 38771897259760730402749

theorem tailTrace_113262 : CollatzResearch.WordTrace tailWord_113262 prefixEnd_113262 38771897259760730402749 := by
  unfold tailWord_113262
  simp only [CollatzResearch.WordTrace]
  refine ⟨516375564459824056835755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2754003010452394969790693 516375564459824056835755)
  ·
    refine ⟨774563346689736085253633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 516375564459824056835755 774563346689736085253633)
    ·
      refine ⟨580922510017302063940225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 774563346689736085253633 580922510017302063940225)
      ·
        refine ⟨435691882512976547955169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580922510017302063940225 435691882512976547955169)
        ·
          refine ⟨326768911884732410966377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435691882512976547955169 326768911884732410966377)
          ·
            refine ⟨245076683913549308224783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326768911884732410966377 245076683913549308224783)
            ·
              refine ⟨367615025870323962337175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245076683913549308224783 367615025870323962337175)
              ·
                refine ⟨551422538805485943505763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367615025870323962337175 551422538805485943505763)
                ·
                  refine ⟨827133808208228915258645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 551422538805485943505763 827133808208228915258645)
                  ·
                    refine ⟨38771897259760730402749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 827133808208228915258645 38771897259760730402749)
                    ·
                      rfl

theorem cell22_113262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_113262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113262 prefixEnd_113262 := by exact prefixLift 113262
  have htrace : WordTrace (prefixWord ++ tailWord_113262) baseStart_113262 baseEnd_113262 := by
    simpa [prefixWord, tailWord_113262, baseEnd_113262] using wordTrace_append hprefix tailTrace_113262
  have hstable : (prefixWord ++ tailWord_113262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113262).length < 2 ^ (prefixWord ++ tailWord_113262).sum := by decide
  have hdescent : baseEnd_113262 < baseStart_113262 := by decide
  rcases family_descends (prefixWord ++ tailWord_113262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113356 : List Nat := [2, 2, 1, 5, 1, 3, 2, 1, 5]
def baseStart_113356 : Nat := 118140960795 + 113356 * 2 ^ 59
def prefixEnd_113356 : Nat := 4983230072969 + 3 ^ 40 * 113356 * 2
def baseEnd_113356 : Nat := 12934691793591939517487

theorem tailTrace_113356 : CollatzResearch.WordTrace tailWord_113356 prefixEnd_113356 12934691793591939517487 := by
  unfold tailWord_113356
  simp only [CollatzResearch.WordTrace]
  refine ⟨2067216488669023254303961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2756288651558697672405281 2067216488669023254303961)
  ·
    refine ⟨1550412366501767440727971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2067216488669023254303961 1550412366501767440727971)
    ·
      refine ⟨2325618549752651161091957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1550412366501767440727971 2325618549752651161091957)
      ·
        refine ⟨218026739039311046352371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2325618549752651161091957 218026739039311046352371)
        ·
          refine ⟨327040108558966569528557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 218026739039311046352371 327040108558966569528557)
          ·
            refine ⟨122640040709612463573209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327040108558966569528557 122640040709612463573209)
            ·
              refine ⟨91980030532209347679907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122640040709612463573209 91980030532209347679907)
              ·
                refine ⟨137970045798314021519861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91980030532209347679907 137970045798314021519861)
                ·
                  refine ⟨12934691793591939517487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137970045798314021519861 12934691793591939517487)
                  ·
                    rfl

theorem cell22_113356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_113356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113356 prefixEnd_113356 := by exact prefixLift 113356
  have htrace : WordTrace (prefixWord ++ tailWord_113356) baseStart_113356 baseEnd_113356 := by
    simpa [prefixWord, tailWord_113356, baseEnd_113356] using wordTrace_append hprefix tailTrace_113356
  have hstable : (prefixWord ++ tailWord_113356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113356).length < 2 ^ (prefixWord ++ tailWord_113356).sum := by decide
  have hdescent : baseEnd_113356 < baseStart_113356 := by decide
  rcases family_descends (prefixWord ++ tailWord_113356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113431 : List Nat := [1, 1, 3, 4, 3, 2, 1, 1, 2, 4]
def baseStart_113431 : Nat := 118140960795 + 113431 * 2 ^ 59
def prefixEnd_113431 : Nat := 4983230072969 + 3 ^ 40 * 113431 * 2
def baseEnd_113431 : Nat := 38829749413500622927231

theorem tailTrace_113431 : CollatzResearch.WordTrace tailWord_113431 prefixEnd_113431 38829749413500622927231 := by
  unfold tailWord_113431
  simp only [CollatzResearch.WordTrace]
  refine ⟨4137168452066334317588147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2758112301377556211725431 4137168452066334317588147)
  ·
    refine ⟨6205752678099501476382221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4137168452066334317588147 6205752678099501476382221)
    ·
      refine ⟨2327157254287313053643333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6205752678099501476382221 2327157254287313053643333)
      ·
        refine ⟨436341985178871197558125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2327157254287313053643333 436341985178871197558125)
        ·
          refine ⟨163628244442076699084297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436341985178871197558125 163628244442076699084297)
          ·
            refine ⟨122721183331557524313223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163628244442076699084297 122721183331557524313223)
            ·
              refine ⟨184081774997336286469835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122721183331557524313223 184081774997336286469835)
              ·
                refine ⟨276122662496004429704753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184081774997336286469835 276122662496004429704753)
                ·
                  refine ⟨207091996872003322278565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 276122662496004429704753 207091996872003322278565)
                  ·
                    refine ⟨38829749413500622927231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 207091996872003322278565 38829749413500622927231)
                    ·
                      rfl

theorem cell22_113431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_113431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113431 prefixEnd_113431 := by exact prefixLift 113431
  have htrace : WordTrace (prefixWord ++ tailWord_113431) baseStart_113431 baseEnd_113431 := by
    simpa [prefixWord, tailWord_113431, baseEnd_113431] using wordTrace_append hprefix tailTrace_113431
  have hstable : (prefixWord ++ tailWord_113431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113431).length < 2 ^ (prefixWord ++ tailWord_113431).sum := by decide
  have hdescent : baseEnd_113431 < baseStart_113431 := by decide
  rcases family_descends (prefixWord ++ tailWord_113431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113450 : List Nat := [3, 1, 4, 3, 1, 2, 1, 2, 2, 3]
def baseStart_113450 : Nat := 118140960795 + 113450 * 2 ^ 59
def prefixEnd_113450 : Nat := 4983230072969 + 3 ^ 40 * 113450 * 2
def baseEnd_113450 : Nat := 38836253501790906702173

theorem tailTrace_113450 : CollatzResearch.WordTrace tailWord_113450 prefixEnd_113450 38836253501790906702173 := by
  unfold tailWord_113450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034465359749375140632451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2758574292665000375019869 1034465359749375140632451)
  ·
    refine ⟨1551698039624062710948677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1034465359749375140632451 1551698039624062710948677)
    ·
      refine ⟨290943382429511758302877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1551698039624062710948677 290943382429511758302877)
      ·
        refine ⟨109103768411066909363579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290943382429511758302877 109103768411066909363579)
        ·
          refine ⟨163655652616600364045369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109103768411066909363579 163655652616600364045369)
          ·
            refine ⟨122741739462450273034027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163655652616600364045369 122741739462450273034027)
            ·
              refine ⟨184112609193675409551041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122741739462450273034027 184112609193675409551041)
              ·
                refine ⟨138084456895256557163281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184112609193675409551041 138084456895256557163281)
                ·
                  refine ⟨103563342671442417872461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138084456895256557163281 103563342671442417872461)
                  ·
                    refine ⟨38836253501790906702173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103563342671442417872461 38836253501790906702173)
                    ·
                      rfl

theorem cell22_113450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_113450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113450 prefixEnd_113450 := by exact prefixLift 113450
  have htrace : WordTrace (prefixWord ++ tailWord_113450) baseStart_113450 baseEnd_113450 := by
    simpa [prefixWord, tailWord_113450, baseEnd_113450] using wordTrace_append hprefix tailTrace_113450
  have hstable : (prefixWord ++ tailWord_113450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113450).length < 2 ^ (prefixWord ++ tailWord_113450).sum := by decide
  have hdescent : baseEnd_113450 < baseStart_113450 := by decide
  rcases family_descends (prefixWord ++ tailWord_113450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113457 : List Nat := [1, 2, 2, 3, 2, 1, 3, 1, 7]
def baseStart_113457 : Nat := 118140960795 + 113457 * 2 ^ 59
def prefixEnd_113457 : Nat := 4983230072969 + 3 ^ 40 * 113457 * 2
def baseEnd_113457 : Nat := 12946216581615073925717

theorem tailTrace_113457 : CollatzResearch.WordTrace tailWord_113457 prefixEnd_113457 12946216581615073925717 := by
  unfold tailWord_113457
  simp only [CollatzResearch.WordTrace]
  refine ⟨4138116749972140758034625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2758744499981427172023083 4138116749972140758034625)
  ·
    refine ⟨3103587562479105568525969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4138116749972140758034625 3103587562479105568525969)
    ·
      refine ⟨2327690671859329176394477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3103587562479105568525969 2327690671859329176394477)
      ·
        refine ⟨872884001947248441147929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2327690671859329176394477 872884001947248441147929)
        ·
          refine ⟨654663001460436330860947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 872884001947248441147929 654663001460436330860947)
          ·
            refine ⟨981994502190654496291421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654663001460436330860947 981994502190654496291421)
            ·
              refine ⟨368247938321495436109283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 981994502190654496291421 368247938321495436109283)
              ·
                refine ⟨552371907482243154163925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 368247938321495436109283 552371907482243154163925)
                ·
                  refine ⟨12946216581615073925717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 552371907482243154163925 12946216581615073925717)
                  ·
                    rfl

theorem cell22_113457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_113457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113457 prefixEnd_113457 := by exact prefixLift 113457
  have htrace : WordTrace (prefixWord ++ tailWord_113457) baseStart_113457 baseEnd_113457 := by
    simpa [prefixWord, tailWord_113457, baseEnd_113457] using wordTrace_append hprefix tailTrace_113457
  have hstable : (prefixWord ++ tailWord_113457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113457).length < 2 ^ (prefixWord ++ tailWord_113457).sum := by decide
  have hdescent : baseEnd_113457 < baseStart_113457 := by decide
  rcases family_descends (prefixWord ++ tailWord_113457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113461 : List Nat := [1, 3, 3, 1, 3, 2, 2, 1, 3, 3]
def baseStart_113461 : Nat := 118140960795 + 113461 * 2 ^ 59
def prefixEnd_113461 : Nat := 4983230072969 + 3 ^ 40 * 113461 * 2
def baseEnd_113461 : Nat := 38840019026590544677139

theorem tailTrace_113461 : CollatzResearch.WordTrace tailWord_113461 prefixEnd_113461 38840019026590544677139 := by
  unfold tailWord_113461
  simp only [CollatzResearch.WordTrace]
  refine ⟨4138262641957649441180237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2758841761305099627453491 4138262641957649441180237)
  ·
    refine ⟨1551848490734118540442589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4138262641957649441180237 1551848490734118540442589)
    ·
      refine ⟨581943184025294452665971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1551848490734118540442589 581943184025294452665971)
      ·
        refine ⟨872914776037941678998957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581943184025294452665971 872914776037941678998957)
        ·
          refine ⟨327343041014228129624609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 872914776037941678998957 327343041014228129624609)
          ·
            refine ⟨245507280760671097218457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327343041014228129624609 245507280760671097218457)
            ·
              refine ⟨184130460570503322913843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245507280760671097218457 184130460570503322913843)
              ·
                refine ⟨276195690855754984370765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 184130460570503322913843 276195690855754984370765)
                ·
                  refine ⟨103573384070908119139037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 276195690855754984370765 103573384070908119139037)
                  ·
                    refine ⟨38840019026590544677139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 103573384070908119139037 38840019026590544677139)
                    ·
                      rfl

theorem cell22_113461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_113461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113461 prefixEnd_113461 := by exact prefixLift 113461
  have htrace : WordTrace (prefixWord ++ tailWord_113461) baseStart_113461 baseEnd_113461 := by
    simpa [prefixWord, tailWord_113461, baseEnd_113461] using wordTrace_append hprefix tailTrace_113461
  have hstable : (prefixWord ++ tailWord_113461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113461).length < 2 ^ (prefixWord ++ tailWord_113461).sum := by decide
  have hdescent : baseEnd_113461 < baseStart_113461 := by decide
  rcases family_descends (prefixWord ++ tailWord_113461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113504 : List Nat := [2, 1, 1, 3, 3, 1, 1, 5, 1, 4]
def baseStart_113504 : Nat := 118140960795 + 113504 * 2 ^ 59
def prefixEnd_113504 : Nat := 4983230072969 + 3 ^ 40 * 113504 * 2
def baseEnd_113504 : Nat := 38854738805352765852007

theorem tailTrace_113504 : CollatzResearch.WordTrace tailWord_113504 prefixEnd_113504 38854738805352765852007 := by
  unfold tailWord_113504
  simp only [CollatzResearch.WordTrace]
  refine ⟨2069915490400933892497783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2759887320534578523330377 2069915490400933892497783)
  ·
    refine ⟨3104873235601400838746675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2069915490400933892497783 3104873235601400838746675)
    ·
      refine ⟨4657309853402101258120013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3104873235601400838746675 4657309853402101258120013)
      ·
        refine ⟨1746491195025787971795005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4657309853402101258120013 1746491195025787971795005)
        ·
          refine ⟨654934198134670489423127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1746491195025787971795005 654934198134670489423127)
          ·
            refine ⟨982401297202005734134691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654934198134670489423127 982401297202005734134691)
            ·
              refine ⟨1473601945803008601202037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982401297202005734134691 1473601945803008601202037)
              ·
                refine ⟨138150182419032056362691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1473601945803008601202037 138150182419032056362691)
                ·
                  refine ⟨207225273628548084544037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138150182419032056362691 207225273628548084544037)
                  ·
                    refine ⟨38854738805352765852007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 207225273628548084544037 38854738805352765852007)
                    ·
                      rfl

theorem cell22_113504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_113504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113504 prefixEnd_113504 := by exact prefixLift 113504
  have htrace : WordTrace (prefixWord ++ tailWord_113504) baseStart_113504 baseEnd_113504 := by
    simpa [prefixWord, tailWord_113504, baseEnd_113504] using wordTrace_append hprefix tailTrace_113504
  have hstable : (prefixWord ++ tailWord_113504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113504).length < 2 ^ (prefixWord ++ tailWord_113504).sum := by decide
  have hdescent : baseEnd_113504 < baseStart_113504 := by decide
  rcases family_descends (prefixWord ++ tailWord_113504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113519 : List Nat := [1, 1, 2, 1, 3, 1, 1, 8, 4]
def baseStart_113519 : Nat := 118140960795 + 113519 * 2 ^ 59
def prefixEnd_113519 : Nat := 4983230072969 + 3 ^ 40 * 113519 * 2
def baseEnd_113519 : Nat := 12953291203965908908987

theorem tailTrace_113519 : CollatzResearch.WordTrace tailWord_113519 prefixEnd_113519 12953291203965908908987 := by
  unfold tailWord_113519
  simp only [CollatzResearch.WordTrace]
  refine ⟨4140378075747525346791611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2760252050498350231194407 4140378075747525346791611)
  ·
    refine ⟨6210567113621288020187417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4140378075747525346791611 6210567113621288020187417)
    ·
      refine ⟨4657925335215966015140563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6210567113621288020187417 4657925335215966015140563)
      ·
        refine ⟨6986888002823949022710845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4657925335215966015140563 6986888002823949022710845)
        ·
          refine ⟨2620083001058980883516567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6986888002823949022710845 2620083001058980883516567)
          ·
            refine ⟨3930124501588471325274851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620083001058980883516567 3930124501588471325274851)
            ·
              refine ⟨5895186752382706987912277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930124501588471325274851 5895186752382706987912277)
              ·
                refine ⟨69084219754484847514597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5895186752382706987912277 69084219754484847514597)
                ·
                  refine ⟨12953291203965908908987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69084219754484847514597 12953291203965908908987)
                  ·
                    rfl

theorem cell22_113519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 4].length) (baseStart_113519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113519 prefixEnd_113519 := by exact prefixLift 113519
  have htrace : WordTrace (prefixWord ++ tailWord_113519) baseStart_113519 baseEnd_113519 := by
    simpa [prefixWord, tailWord_113519, baseEnd_113519] using wordTrace_append hprefix tailTrace_113519
  have hstable : (prefixWord ++ tailWord_113519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113519).length < 2 ^ (prefixWord ++ tailWord_113519).sum := by decide
  have hdescent : baseEnd_113519 < baseStart_113519 := by decide
  rcases family_descends (prefixWord ++ tailWord_113519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113532 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_113532 : Nat := 118140960795 + 113532 * 2 ^ 59
def prefixEnd_113532 : Nat := 4983230072969 + 3 ^ 40 * 113532 * 2
def baseEnd_113532 : Nat := 38864323777570026151921

theorem tailTrace_113532 : CollatzResearch.WordTrace tailWord_113532 prefixEnd_113532 38864323777570026151921 := by
  unfold tailWord_113532
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070426112350214283507425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2760568149800285711343233 2070426112350214283507425)
  ·
    refine ⟨1552819584262660712630569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2070426112350214283507425 1552819584262660712630569)
    ·
      refine ⟨1164614688196995534472927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1552819584262660712630569 1164614688196995534472927)
      ·
        refine ⟨1746922032295493301709391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164614688196995534472927 1746922032295493301709391)
        ·
          refine ⟨2620383048443239952564087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1746922032295493301709391 2620383048443239952564087)
          ·
            refine ⟨3930574572664859928846131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2620383048443239952564087 3930574572664859928846131)
            ·
              refine ⟨5895861858997289893269197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3930574572664859928846131 5895861858997289893269197)
              ·
                refine ⟨2210948197123983709975949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5895861858997289893269197 2210948197123983709975949)
                ·
                  refine ⟨829105573921493891240981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2210948197123983709975949 829105573921493891240981)
                  ·
                    refine ⟨38864323777570026151921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 829105573921493891240981 38864323777570026151921)
                    ·
                      rfl

theorem cell22_113532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_113532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113532 prefixEnd_113532 := by exact prefixLift 113532
  have htrace : WordTrace (prefixWord ++ tailWord_113532) baseStart_113532 baseEnd_113532 := by
    simpa [prefixWord, tailWord_113532, baseEnd_113532] using wordTrace_append hprefix tailTrace_113532
  have hstable : (prefixWord ++ tailWord_113532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113532).length < 2 ^ (prefixWord ++ tailWord_113532).sum := by decide
  have hdescent : baseEnd_113532 < baseStart_113532 := by decide
  rcases family_descends (prefixWord ++ tailWord_113532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113547 : List Nat := [1, 1, 1, 1, 4, 2, 4, 8]
def baseStart_113547 : Nat := 118140960795 + 113547 * 2 ^ 59
def prefixEnd_113547 : Nat := 4983230072969 + 3 ^ 40 * 113547 * 2
def baseEnd_113547 : Nat := 4318828731568331891875

theorem tailTrace_113547 : CollatzResearch.WordTrace tailWord_113547 prefixEnd_113547 4318828731568331891875 := by
  unfold tailWord_113547
  simp only [CollatzResearch.WordTrace]
  refine ⟨4141399319646086128810895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2760932879764057419207263 4141399319646086128810895)
  ·
    refine ⟨6212098979469129193216343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4141399319646086128810895 6212098979469129193216343)
    ·
      refine ⟨9318148469203693789824515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6212098979469129193216343 9318148469203693789824515)
      ·
        refine ⟨13977222703805540684736773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9318148469203693789824515 13977222703805540684736773)
        ·
          refine ⟨2620729256963538878388145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13977222703805540684736773 2620729256963538878388145)
          ·
            refine ⟨1965546942722654158791109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2620729256963538878388145 1965546942722654158791109)
            ·
              refine ⟨368540051760497654773333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1965546942722654158791109 368540051760497654773333)
              ·
                refine ⟨4318828731568331891875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 368540051760497654773333 4318828731568331891875)
                ·
                  rfl

theorem cell22_113547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 8].length) (baseStart_113547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113547 prefixEnd_113547 := by exact prefixLift 113547
  have htrace : WordTrace (prefixWord ++ tailWord_113547) baseStart_113547 baseEnd_113547 := by
    simpa [prefixWord, tailWord_113547, baseEnd_113547] using wordTrace_append hprefix tailTrace_113547
  have hstable : (prefixWord ++ tailWord_113547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113547).length < 2 ^ (prefixWord ++ tailWord_113547).sum := by decide
  have hdescent : baseEnd_113547 < baseStart_113547 := by decide
  rcases family_descends (prefixWord ++ tailWord_113547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113564 : List Nat := [2, 2, 3, 3, 2, 10]
def baseStart_113564 : Nat := 118140960795 + 113564 * 2 ^ 59
def prefixEnd_113564 : Nat := 4983230072969 + 3 ^ 40 * 113564 * 2
def baseEnd_113564 : Nat := 479941704092995177183

theorem tailTrace_113564 : CollatzResearch.WordTrace tailWord_113564 prefixEnd_113564 479941704092995177183 := by
  unfold tailWord_113564
  simp only [CollatzResearch.WordTrace]
  refine ⟨2071009680292249016089873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2761346240389665354786497 2071009680292249016089873)
  ·
    refine ⟨1553257260219186762067405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2071009680292249016089873 1553257260219186762067405)
    ·
      refine ⟨582471472582195035775277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1553257260219186762067405 582471472582195035775277)
      ·
        refine ⟨218426802218323138415729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 582471472582195035775277 218426802218323138415729)
        ·
          refine ⟨163820101663742353811797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218426802218323138415729 163820101663742353811797)
          ·
            refine ⟨479941704092995177183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 163820101663742353811797 479941704092995177183)
            ·
              rfl

theorem cell22_113564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 10].length) (baseStart_113564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113564 prefixEnd_113564 := by exact prefixLift 113564
  have htrace : WordTrace (prefixWord ++ tailWord_113564) baseStart_113564 baseEnd_113564 := by
    simpa [prefixWord, tailWord_113564, baseEnd_113564] using wordTrace_append hprefix tailTrace_113564
  have hstable : (prefixWord ++ tailWord_113564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113564).length < 2 ^ (prefixWord ++ tailWord_113564).sum := by decide
  have hdescent : baseEnd_113564 < baseStart_113564 := by decide
  rcases family_descends (prefixWord ++ tailWord_113564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113570 : List Nat := [3, 3, 1, 2, 2, 3, 2, 2, 4]
def baseStart_113570 : Nat := 118140960795 + 113570 * 2 ^ 59
def prefixEnd_113570 : Nat := 4983230072969 + 3 ^ 40 * 113570 * 2
def baseEnd_113570 : Nat := 12959110651383531233935

theorem tailTrace_113570 : CollatzResearch.WordTrace tailWord_113570 prefixEnd_113570 12959110651383531233935 := by
  unfold tailWord_113570
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035559549640690264224541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2761492132375174037932109 1035559549640690264224541)
  ·
    refine ⟨388334831115258849084203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1035559549640690264224541 388334831115258849084203)
    ·
      refine ⟨582502246672888273626305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388334831115258849084203 582502246672888273626305)
      ·
        refine ⟨436876685004666205219729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582502246672888273626305 436876685004666205219729)
        ·
          refine ⟨327657513753499653914797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436876685004666205219729 327657513753499653914797)
          ·
            refine ⟨122871567657562370218049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327657513753499653914797 122871567657562370218049)
            ·
              refine ⟨92153675743171777663537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122871567657562370218049 92153675743171777663537)
              ·
                refine ⟨69115256807378833247653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92153675743171777663537 69115256807378833247653)
                ·
                  refine ⟨12959110651383531233935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69115256807378833247653 12959110651383531233935)
                  ·
                    rfl

theorem cell22_113570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_113570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113570 prefixEnd_113570 := by exact prefixLift 113570
  have htrace : WordTrace (prefixWord ++ tailWord_113570) baseStart_113570 baseEnd_113570 := by
    simpa [prefixWord, tailWord_113570, baseEnd_113570] using wordTrace_append hprefix tailTrace_113570
  have hstable : (prefixWord ++ tailWord_113570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113570).length < 2 ^ (prefixWord ++ tailWord_113570).sum := by decide
  have hdescent : baseEnd_113570 < baseStart_113570 := by decide
  rcases family_descends (prefixWord ++ tailWord_113570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113577 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 1, 8]
def baseStart_113577 : Nat := 118140960795 + 113577 * 2 ^ 59
def prefixEnd_113577 : Nat := 4983230072969 + 3 ^ 40 * 113577 * 2
def baseEnd_113577 : Nat := 38879728197204908776783

theorem tailTrace_113577 : CollatzResearch.WordTrace tailWord_113577 prefixEnd_113577 38879728197204908776783 := by
  unfold tailWord_113577
  simp only [CollatzResearch.WordTrace]
  refine ⟨4142493509537401252402985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2761662339691600834935323 4142493509537401252402985)
  ·
    refine ⟨3106870132153050939302239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4142493509537401252402985 3106870132153050939302239)
    ·
      refine ⟨4660305198229576408953359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3106870132153050939302239 4660305198229576408953359)
      ·
        refine ⟨6990457797344364613430039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4660305198229576408953359 6990457797344364613430039)
        ·
          refine ⟨10485686696016546920145059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6990457797344364613430039 10485686696016546920145059)
          ·
            refine ⟨15728530044024820380217589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10485686696016546920145059 15728530044024820380217589)
            ·
              refine ⟨1474549691627326910645399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15728530044024820380217589 1474549691627326910645399)
              ·
                refine ⟨2211824537440990365968099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474549691627326910645399 2211824537440990365968099)
                ·
                  refine ⟨3317736806161485548952149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2211824537440990365968099 3317736806161485548952149)
                  ·
                    refine ⟨38879728197204908776783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 3317736806161485548952149 38879728197204908776783)
                    ·
                      rfl

theorem cell22_113577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_113577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113577 prefixEnd_113577 := by exact prefixLift 113577
  have htrace : WordTrace (prefixWord ++ tailWord_113577) baseStart_113577 baseEnd_113577 := by
    simpa [prefixWord, tailWord_113577, baseEnd_113577] using wordTrace_append hprefix tailTrace_113577
  have hstable : (prefixWord ++ tailWord_113577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113577).length < 2 ^ (prefixWord ++ tailWord_113577).sum := by decide
  have hdescent : baseEnd_113577 < baseStart_113577 := by decide
  rcases family_descends (prefixWord ++ tailWord_113577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113606 : List Nat := [6, 1, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_113606 : Nat := 118140960795 + 113606 * 2 ^ 59
def prefixEnd_113606 : Nat := 4983230072969 + 3 ^ 40 * 113606 * 2
def baseEnd_113606 : Nat := 38889655489858499801695

theorem tailTrace_113606 : CollatzResearch.WordTrace tailWord_113606 prefixEnd_113606 38889655489858499801695 := by
  unfold tailWord_113606
  simp only [CollatzResearch.WordTrace]
  refine ⟨129485975826010600162771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2762367484288226136805781 129485975826010600162771)
  ·
    refine ⟨194228963739015900244157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129485975826010600162771 194228963739015900244157)
    ·
      refine ⟨72835861402130962591559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 194228963739015900244157 72835861402130962591559)
      ·
        refine ⟨109253792103196443887339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72835861402130962591559 109253792103196443887339)
        ·
          refine ⟨163880688154794665831009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109253792103196443887339 163880688154794665831009)
          ·
            refine ⟨122910516116095999373257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163880688154794665831009 122910516116095999373257)
            ·
              refine ⟨92182887087071999529943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122910516116095999373257 92182887087071999529943)
              ·
                refine ⟨138274330630607999294915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92182887087071999529943 138274330630607999294915)
                ·
                  refine ⟨207411495945911998942373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138274330630607999294915 207411495945911998942373)
                  ·
                    refine ⟨38889655489858499801695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 207411495945911998942373 38889655489858499801695)
                    ·
                      rfl

theorem cell22_113606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_113606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113606 prefixEnd_113606 := by exact prefixLift 113606
  have htrace : WordTrace (prefixWord ++ tailWord_113606) baseStart_113606 baseEnd_113606 := by
    simpa [prefixWord, tailWord_113606, baseEnd_113606] using wordTrace_append hprefix tailTrace_113606
  have hstable : (prefixWord ++ tailWord_113606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113606).length < 2 ^ (prefixWord ++ tailWord_113606).sum := by decide
  have hdescent : baseEnd_113606 < baseStart_113606 := by decide
  rcases family_descends (prefixWord ++ tailWord_113606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113624 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 2, 5]
def baseStart_113624 : Nat := 118140960795 + 113624 * 2 ^ 59
def prefixEnd_113624 : Nat := 4983230072969 + 3 ^ 40 * 113624 * 2
def baseEnd_113624 : Nat := 38895817257712452851639

theorem tailTrace_113624 : CollatzResearch.WordTrace tailWord_113624 prefixEnd_113624 38895817257712452851639 := by
  unfold tailWord_113624
  simp only [CollatzResearch.WordTrace]
  refine ⟨2072103870183564139681963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2762805160244752186242617 2072103870183564139681963)
  ·
    refine ⟨3108155805275346209522945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2072103870183564139681963 3108155805275346209522945)
    ·
      refine ⟨2331116853956509657142209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3108155805275346209522945 2331116853956509657142209)
      ·
        refine ⟨1748337640467382242856657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2331116853956509657142209 1748337640467382242856657)
        ·
          refine ⟨1311253230350536682142493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1748337640467382242856657 1311253230350536682142493)
          ·
            refine ⟨491719961381451255803435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1311253230350536682142493 491719961381451255803435)
            ·
              refine ⟨737579942072176883705153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491719961381451255803435 737579942072176883705153)
              ·
                refine ⟨553184956554132662778865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737579942072176883705153 553184956554132662778865)
                ·
                  refine ⟨414888717415599497084149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553184956554132662778865 414888717415599497084149)
                  ·
                    refine ⟨38895817257712452851639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 414888717415599497084149 38895817257712452851639)
                    ·
                      rfl

theorem cell22_113624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_113624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_113624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_113624 prefixEnd_113624 := by exact prefixLift 113624
  have htrace : WordTrace (prefixWord ++ tailWord_113624) baseStart_113624 baseEnd_113624 := by
    simpa [prefixWord, tailWord_113624, baseEnd_113624] using wordTrace_append hprefix tailTrace_113624
  have hstable : (prefixWord ++ tailWord_113624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113624).length < 2 ^ (prefixWord ++ tailWord_113624).sum := by decide
  have hdescent : baseEnd_113624 < baseStart_113624 := by decide
  rcases family_descends (prefixWord ++ tailWord_113624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
