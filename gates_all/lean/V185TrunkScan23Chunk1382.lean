import V185TrunkScan23Chunk1381

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8185633 : List Nat := [1, 2, 3, 2, 1, 5, 1, 1, 7]
def baseStart_8185633 : Nat := 118140960795 + 8185633 * 2 ^ 59
def prefixEnd_8185633 : Nat := 4983230072969 + 3 ^ 40 * 8185633 * 2
def baseEnd_8185633 : Nat := 467018243367208600771385

theorem tailTrace_8185633 : CollatzResearch.WordTrace tailWord_8185633 prefixEnd_8185633 467018243367208600771385 := by
  unfold tailWord_8185633
  simp only [CollatzResearch.WordTrace]
  refine ⟨298554562753857110661457553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199036375169238073774305035 298554562753857110661457553)
  ·
    refine ⟨223915922065392832996093165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298554562753857110661457553 223915922065392832996093165)
    ·
      refine ⟨83968470774522312373534937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223915922065392832996093165 83968470774522312373534937)
      ·
        refine ⟨62976353080891734280151203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83968470774522312373534937 62976353080891734280151203)
        ·
          refine ⟨94464529621337601420226805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62976353080891734280151203 94464529621337601420226805)
          ·
            refine ⟨8856049652000400133146263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94464529621337601420226805 8856049652000400133146263)
            ·
              refine ⟨13284074478000600199719395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8856049652000400133146263 13284074478000600199719395)
              ·
                refine ⟨19926111717000900299579093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13284074478000600199719395 19926111717000900299579093)
                ·
                  refine ⟨467018243367208600771385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19926111717000900299579093 467018243367208600771385)
                  ·
                    rfl

theorem cell23_8185633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 7].length) (baseStart_8185633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185633 prefixEnd_8185633 := by exact prefixLift 8185633
  have htrace : WordTrace (prefixWord ++ tailWord_8185633) baseStart_8185633 baseEnd_8185633 := by
    simpa [prefixWord, tailWord_8185633, baseEnd_8185633] using wordTrace_append hprefix tailTrace_8185633
  have hstable : (prefixWord ++ tailWord_8185633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185633).length < 2 ^ (prefixWord ++ tailWord_8185633).sum := by decide
  have hdescent : baseEnd_8185633 < baseStart_8185633 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185644 : List Nat := [2, 2, 1, 1, 1, 7, 2, 1, 2, 2, 2]
def baseStart_8185644 : Nat := 118140960795 + 8185644 * 2 ^ 59
def prefixEnd_8185644 : Nat := 4983230072969 + 3 ^ 40 * 8185644 * 2
def baseEnd_8185644 : Nat := 4203169838592076863904915

theorem tailTrace_8185644 : CollatzResearch.WordTrace tailWord_8185644 prefixEnd_8185644 4203169838592076863904915 := by
  unfold tailWord_8185644
  simp only [CollatzResearch.WordTrace]
  refine ⟨149277481978408629770053993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199036642637878173026738657 149277481978408629770053993)
  ·
    refine ⟨111958111483806472327540495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149277481978408629770053993 111958111483806472327540495)
    ·
      refine ⟨167937167225709708491310743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111958111483806472327540495 167937167225709708491310743)
      ·
        refine ⟨251905750838564562736966115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167937167225709708491310743 251905750838564562736966115)
        ·
          refine ⟨377858626257846844105449173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251905750838564562736966115 377858626257846844105449173)
          ·
            refine ⟨8856061552918285408721465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 377858626257846844105449173 8856061552918285408721465)
            ·
              refine ⟨6642046164688714056541099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8856061552918285408721465 6642046164688714056541099)
              ·
                refine ⟨9963069247033071084811649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6642046164688714056541099 9963069247033071084811649)
                ·
                  refine ⟨7472301935274803313608737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9963069247033071084811649 7472301935274803313608737)
                  ·
                    refine ⟨5604226451456102485206553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7472301935274803313608737 5604226451456102485206553)
                    ·
                      refine ⟨4203169838592076863904915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5604226451456102485206553 4203169838592076863904915)
                      ·
                        rfl

theorem cell23_8185644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 2, 2].length) (baseStart_8185644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185644 prefixEnd_8185644 := by exact prefixLift 8185644
  have htrace : WordTrace (prefixWord ++ tailWord_8185644) baseStart_8185644 baseEnd_8185644 := by
    simpa [prefixWord, tailWord_8185644, baseEnd_8185644] using wordTrace_append hprefix tailTrace_8185644
  have hstable : (prefixWord ++ tailWord_8185644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185644).length < 2 ^ (prefixWord ++ tailWord_8185644).sum := by decide
  have hdescent : baseEnd_8185644 < baseStart_8185644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185703 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_8185703 : Nat := 118140960795 + 8185703 * 2 ^ 59
def prefixEnd_8185703 : Nat := 4983230072969 + 3 ^ 40 * 8185703 * 2
def baseEnd_8185703 : Nat := 4203200133950692133067143

theorem tailTrace_8185703 : CollatzResearch.WordTrace tailWord_8185703 prefixEnd_8185703 4203200133950692133067143 := by
  unfold tailWord_8185703
  simp only [CollatzResearch.WordTrace]
  refine ⟨298557115863603512616505763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199038077242402341744337175 298557115863603512616505763)
  ·
    refine ⟨447835673795405268924758645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298557115863603512616505763 447835673795405268924758645)
    ·
      refine ⟨41984594418319243961696123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 447835673795405268924758645 41984594418319243961696123)
      ·
        refine ⟨62976891627478865942544185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41984594418319243961696123 62976891627478865942544185)
        ·
          refine ⟨47232668720609149456908139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62976891627478865942544185 47232668720609149456908139)
          ·
            refine ⟨70849003080913724185362209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47232668720609149456908139 70849003080913724185362209)
            ·
              refine ⟨53136752310685293139021657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70849003080913724185362209 53136752310685293139021657)
              ·
                refine ⟨39852564233013969854266243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53136752310685293139021657 39852564233013969854266243)
                ·
                  refine ⟨59778846349520954781399365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39852564233013969854266243 59778846349520954781399365)
                  ·
                    refine ⟨11208533690535179021512381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59778846349520954781399365 11208533690535179021512381)
                    ·
                      refine ⟨4203200133950692133067143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11208533690535179021512381 4203200133950692133067143)
                      ·
                        rfl

theorem cell23_8185703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_8185703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185703 prefixEnd_8185703 := by exact prefixLift 8185703
  have htrace : WordTrace (prefixWord ++ tailWord_8185703) baseStart_8185703 baseEnd_8185703 := by
    simpa [prefixWord, tailWord_8185703, baseEnd_8185703] using wordTrace_append hprefix tailTrace_8185703
  have hstable : (prefixWord ++ tailWord_8185703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185703).length < 2 ^ (prefixWord ++ tailWord_8185703).sum := by decide
  have hdescent : baseEnd_8185703 < baseStart_8185703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185710 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_8185710 : Nat := 118140960795 + 8185710 * 2 ^ 59
def prefixEnd_8185710 : Nat := 4983230072969 + 3 ^ 40 * 8185710 * 2
def baseEnd_8185710 : Nat := 1401067909438424535226537

theorem tailTrace_8185710 : CollatzResearch.WordTrace tailWord_8185710 prefixEnd_8185710 1401067909438424535226537 := by
  unfold tailWord_8185710
  simp only [CollatzResearch.WordTrace]
  refine ⟨37319671396822269101501323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199038247449718768541340389 37319671396822269101501323)
  ·
    refine ⟨55979507095233403652251985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37319671396822269101501323 55979507095233403652251985)
    ·
      refine ⟨41984630321425052739188989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55979507095233403652251985 41984630321425052739188989)
      ·
        refine ⟨15744236370534394777195871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41984630321425052739188989 15744236370534394777195871)
        ·
          refine ⟨23616354555801592165793807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15744236370534394777195871 23616354555801592165793807)
          ·
            refine ⟨35424531833702388248690711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23616354555801592165793807 35424531833702388248690711)
            ·
              refine ⟨53136797750553582373036067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35424531833702388248690711 53136797750553582373036067)
              ·
                refine ⟨79705196625830373559554101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53136797750553582373036067 79705196625830373559554101)
                ·
                  refine ⟨7472362183671597521208197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79705196625830373559554101 7472362183671597521208197)
                  ·
                    refine ⟨1401067909438424535226537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7472362183671597521208197 1401067909438424535226537)
                    ·
                      rfl

theorem cell23_8185710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_8185710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185710 prefixEnd_8185710 := by exact prefixLift 8185710
  have htrace : WordTrace (prefixWord ++ tailWord_8185710) baseStart_8185710 baseEnd_8185710 := by
    simpa [prefixWord, tailWord_8185710, baseEnd_8185710] using wordTrace_append hprefix tailTrace_8185710
  have hstable : (prefixWord ++ tailWord_8185710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185710).length < 2 ^ (prefixWord ++ tailWord_8185710).sum := by decide
  have hdescent : baseEnd_8185710 < baseStart_8185710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185767 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_8185767 : Nat := 118140960795 + 8185767 * 2 ^ 59
def prefixEnd_8185767 : Nat := 4983230072969 + 3 ^ 40 * 8185767 * 2
def baseEnd_8185767 : Nat := 4203232996712579882666849

theorem tailTrace_8185767 : CollatzResearch.WordTrace tailWord_8185767 prefixEnd_8185767 4203232996712579882666849 := by
  unfold tailWord_8185767
  simp only [CollatzResearch.WordTrace]
  refine ⟨298559450135371651546835555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199039633423581101031223703 298559450135371651546835555)
  ·
    refine ⟨447839175203057477320253333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298559450135371651546835555 447839175203057477320253333)
    ·
      refine ⟨20992461337643319249386875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 447839175203057477320253333 20992461337643319249386875)
      ·
        refine ⟨31488692006464978874080313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20992461337643319249386875 31488692006464978874080313)
        ·
          refine ⟨23616519004848734155560235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31488692006464978874080313 23616519004848734155560235)
          ·
            refine ⟨35424778507273101233340353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23616519004848734155560235 35424778507273101233340353)
            ·
              refine ⟨26568583880454825925005265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35424778507273101233340353 26568583880454825925005265)
              ·
                refine ⟨19926437910341119443753949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26568583880454825925005265 19926437910341119443753949)
                ·
                  refine ⟨7472414216377919791407731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19926437910341119443753949 7472414216377919791407731)
                  ·
                    refine ⟨11208621324566879687111597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7472414216377919791407731 11208621324566879687111597)
                    ·
                      refine ⟨4203232996712579882666849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11208621324566879687111597 4203232996712579882666849)
                      ·
                        rfl

theorem cell23_8185767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_8185767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185767 prefixEnd_8185767 := by exact prefixLift 8185767
  have htrace : WordTrace (prefixWord ++ tailWord_8185767) baseStart_8185767 baseEnd_8185767 := by
    simpa [prefixWord, tailWord_8185767, baseEnd_8185767] using wordTrace_append hprefix tailTrace_8185767
  have hstable : (prefixWord ++ tailWord_8185767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185767).length < 2 ^ (prefixWord ++ tailWord_8185767).sum := by decide
  have hdescent : baseEnd_8185767 < baseStart_8185767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185800 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 4, 4]
def baseStart_8185800 : Nat := 118140960795 + 8185800 * 2 ^ 59
def prefixEnd_8185800 : Nat := 4983230072969 + 3 ^ 40 * 8185800 * 2
def baseEnd_8185800 : Nat := 1401083313858059417851399

theorem tailTrace_8185800 : CollatzResearch.WordTrace tailWord_8185800 prefixEnd_8185800 1401083313858059417851399 := by
  unfold tailWord_8185800
  simp only [CollatzResearch.WordTrace]
  refine ⟨149280326872126049091393427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199040435829501398788524569 149280326872126049091393427)
  ·
    refine ⟨223920490308189073637090141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149280326872126049091393427 223920490308189073637090141)
    ·
      refine ⟨83970183865570902613908803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223920490308189073637090141 83970183865570902613908803)
      ·
        refine ⟨125955275798356353920863205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83970183865570902613908803 125955275798356353920863205)
        ·
          refine ⟨23616614212191816360161851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125955275798356353920863205 23616614212191816360161851)
          ·
            refine ⟨35424921318287724540242777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23616614212191816360161851 35424921318287724540242777)
            ·
              refine ⟨26568690988715793405182083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35424921318287724540242777 26568690988715793405182083)
              ·
                refine ⟨39853036483073690107773125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26568690988715793405182083 39853036483073690107773125)
                ·
                  refine ⟨7472444340576316895207461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39853036483073690107773125 7472444340576316895207461)
                  ·
                    refine ⟨1401083313858059417851399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7472444340576316895207461 1401083313858059417851399)
                    ·
                      rfl

theorem cell23_8185800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_8185800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185800 prefixEnd_8185800 := by exact prefixLift 8185800
  have htrace : WordTrace (prefixWord ++ tailWord_8185800) baseStart_8185800 baseEnd_8185800 := by
    simpa [prefixWord, tailWord_8185800, baseEnd_8185800] using wordTrace_append hprefix tailTrace_8185800
  have hstable : (prefixWord ++ tailWord_8185800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185800).length < 2 ^ (prefixWord ++ tailWord_8185800).sum := by decide
  have hdescent : baseEnd_8185800 < baseStart_8185800 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185813 : List Nat := [1, 3, 2, 3, 2, 1, 1, 10]
def baseStart_8185813 : Nat := 118140960795 + 8185813 * 2 ^ 59
def prefixEnd_8185813 : Nat := 4983230072969 + 3 ^ 40 * 8185813 * 2
def baseEnd_8185813 : Nat := 155676170993432840840431

theorem tailTrace_8185813 : CollatzResearch.WordTrace tailWord_8185813 prefixEnd_8185813 155676170993432840840431 := by
  unfold tailWord_8185813
  simp only [CollatzResearch.WordTrace]
  refine ⟨298561127893205001403010093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199040751928803334268673395 298561127893205001403010093)
  ·
    refine ⟨111960422959951875526128785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298561127893205001403010093 111960422959951875526128785)
    ·
      refine ⟨83970317219963906644596589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111960422959951875526128785 83970317219963906644596589)
      ·
        refine ⟨31488868957486464991723721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83970317219963906644596589 31488868957486464991723721)
        ·
          refine ⟨23616651718114848743792791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31488868957486464991723721 23616651718114848743792791)
          ·
            refine ⟨35424977577172273115689187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23616651718114848743792791 35424977577172273115689187)
            ·
              refine ⟨53137466365758409673533781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35424977577172273115689187 53137466365758409673533781)
              ·
                refine ⟨155676170993432840840431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53137466365758409673533781 155676170993432840840431)
                ·
                  rfl

theorem cell23_8185813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 10].length) (baseStart_8185813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185813 prefixEnd_8185813 := by exact prefixLift 8185813
  have htrace : WordTrace (prefixWord ++ tailWord_8185813) baseStart_8185813 baseEnd_8185813 := by
    simpa [prefixWord, tailWord_8185813, baseEnd_8185813] using wordTrace_append hprefix tailTrace_8185813
  have hstable : (prefixWord ++ tailWord_8185813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185813).length < 2 ^ (prefixWord ++ tailWord_8185813).sum := by decide
  have hdescent : baseEnd_8185813 < baseStart_8185813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185817 : List Nat := [1, 2, 1, 2, 6, 1, 1, 3, 2, 4]
def baseStart_8185817 : Nat := 118140960795 + 8185817 * 2 ^ 59
def prefixEnd_8185817 : Nat := 4983230072969 + 3 ^ 40 * 8185817 * 2
def baseEnd_8185817 : Nat := 1401086223581768229013873

theorem tailTrace_8185817 : CollatzResearch.WordTrace tailWord_8185817 prefixEnd_8185817 1401086223581768229013873 := by
  unfold tailWord_8185817
  simp only [CollatzResearch.WordTrace]
  refine ⟨298561273785190510086155705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199040849190127006724103803 298561273785190510086155705)
  ·
    refine ⟨223920955338892882564616779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298561273785190510086155705 223920955338892882564616779)
    ·
      refine ⟨335881433008339323846925169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223920955338892882564616779 335881433008339323846925169)
      ·
        refine ⟨251911074756254492885193877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335881433008339323846925169 251911074756254492885193877)
        ·
          refine ⟨11808331629199429353993463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251911074756254492885193877 11808331629199429353993463)
          ·
            refine ⟨17712497443799144030990195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11808331629199429353993463 17712497443799144030990195)
            ·
              refine ⟨26568746165698716046485293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17712497443799144030990195 26568746165698716046485293)
              ·
                refine ⟨9963279812137018517431985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26568746165698716046485293 9963279812137018517431985)
                ·
                  refine ⟨7472459859102763888073989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9963279812137018517431985 7472459859102763888073989)
                  ·
                    refine ⟨1401086223581768229013873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7472459859102763888073989 1401086223581768229013873)
                    ·
                      rfl

theorem cell23_8185817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 4].length) (baseStart_8185817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185817 prefixEnd_8185817 := by exact prefixLift 8185817
  have htrace : WordTrace (prefixWord ++ tailWord_8185817) baseStart_8185817 baseEnd_8185817 := by
    simpa [prefixWord, tailWord_8185817, baseEnd_8185817] using wordTrace_append hprefix tailTrace_8185817
  have hstable : (prefixWord ++ tailWord_8185817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185817).length < 2 ^ (prefixWord ++ tailWord_8185817).sum := by decide
  have hdescent : baseEnd_8185817 < baseStart_8185817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185827 : List Nat := [1, 1, 1, 6, 1, 2, 3, 2, 1, 2, 3]
def baseStart_8185827 : Nat := 118140960795 + 8185827 * 2 ^ 59
def prefixEnd_8185827 : Nat := 4983230072969 + 3 ^ 40 * 8185827 * 2
def baseEnd_8185827 : Nat := 4203263805551849647916573

theorem tailTrace_8185827 : CollatzResearch.WordTrace tailWord_8185827 prefixEnd_8185827 4203263805551849647916573 := by
  unfold tailWord_8185827
  simp only [CollatzResearch.WordTrace]
  refine ⟨298561638515154281794019735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199041092343436187862679823 298561638515154281794019735)
  ·
    refine ⟨447842457772731422691029603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298561638515154281794019735 447842457772731422691029603)
    ·
      refine ⟨671763686659097134036544405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447842457772731422691029603 671763686659097134036544405)
      ·
        refine ⟨31488922812145178157963019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 671763686659097134036544405 31488922812145178157963019)
        ·
          refine ⟨47233384218217767236944529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31488922812145178157963019 47233384218217767236944529)
          ·
            refine ⟨35425038163663325427708397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47233384218217767236944529 35425038163663325427708397)
            ·
              refine ⟨13284389311373747035390649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35425038163663325427708397 13284389311373747035390649)
              ·
                refine ⟨9963291983530310276542987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13284389311373747035390649 9963291983530310276542987)
                ·
                  refine ⟨14944937975295465414814481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9963291983530310276542987 14944937975295465414814481)
                  ·
                    refine ⟨11208703481471599061110861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14944937975295465414814481 11208703481471599061110861)
                    ·
                      refine ⟨4203263805551849647916573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11208703481471599061110861 4203263805551849647916573)
                      ·
                        rfl

theorem cell23_8185827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_8185827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185827 prefixEnd_8185827 := by exact prefixLift 8185827
  have htrace : WordTrace (prefixWord ++ tailWord_8185827) baseStart_8185827 baseEnd_8185827 := by
    simpa [prefixWord, tailWord_8185827, baseEnd_8185827] using wordTrace_append hprefix tailTrace_8185827
  have hstable : (prefixWord ++ tailWord_8185827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185827).length < 2 ^ (prefixWord ++ tailWord_8185827).sum := by decide
  have hdescent : baseEnd_8185827 < baseStart_8185827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185840 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 6, 1, 3]
def baseStart_8185840 : Nat := 118140960795 + 8185840 * 2 ^ 59
def prefixEnd_8185840 : Nat := 4983230072969 + 3 ^ 40 * 8185840 * 2
def baseEnd_8185840 : Nat := 4203270480800358097054013

theorem tailTrace_8185840 : CollatzResearch.WordTrace tailWord_8185840 prefixEnd_8185840 4203270480800358097054013 := by
  unfold tailWord_8185840
  simp only [CollatzResearch.WordTrace]
  refine ⟨149281056332053592507121487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199041408442738123342828649 149281056332053592507121487)
  ·
    refine ⟨223921584498080388760682231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149281056332053592507121487 223921584498080388760682231)
    ·
      refine ⟨335882376747120583141023347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223921584498080388760682231 335882376747120583141023347)
      ·
        refine ⟨503823565120680874711535021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335882376747120583141023347 503823565120680874711535021)
        ·
          refine ⟨188933836920255328016825633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503823565120680874711535021 188933836920255328016825633)
          ·
            refine ⟨141700377690191496012619225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188933836920255328016825633 141700377690191496012619225)
            ·
              refine ⟨106275283267643622009464419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141700377690191496012619225 106275283267643622009464419)
              ·
                refine ⟨159412924901465433014196629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106275283267643622009464419 159412924901465433014196629)
                ·
                  refine ⟨7472480854756192172540467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159412924901465433014196629 7472480854756192172540467)
                  ·
                    refine ⟨11208721282134288258810701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7472480854756192172540467 11208721282134288258810701)
                    ·
                      refine ⟨4203270480800358097054013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11208721282134288258810701 4203270480800358097054013)
                      ·
                        rfl

theorem cell23_8185840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 6, 1, 3].length) (baseStart_8185840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185840 prefixEnd_8185840 := by exact prefixLift 8185840
  have htrace : WordTrace (prefixWord ++ tailWord_8185840) baseStart_8185840 baseEnd_8185840 := by
    simpa [prefixWord, tailWord_8185840, baseEnd_8185840] using wordTrace_append hprefix tailTrace_8185840
  have hstable : (prefixWord ++ tailWord_8185840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185840).length < 2 ^ (prefixWord ++ tailWord_8185840).sum := by decide
  have hdescent : baseEnd_8185840 < baseStart_8185840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185853 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_8185853 : Nat := 118140960795 + 8185853 * 2 ^ 59
def prefixEnd_8185853 : Nat := 4983230072969 + 3 ^ 40 * 8185853 * 2
def baseEnd_8185853 : Nat := 4203277156048866546191453

theorem tailTrace_8185853 : CollatzResearch.WordTrace tailWord_8185853 prefixEnd_8185853 4203277156048866546191453 := by
  unfold tailWord_8185853
  simp only [CollatzResearch.WordTrace]
  refine ⟨298562586813060088234466213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199041724542040058822977475 298562586813060088234466213)
  ·
    refine ⟨55980485027448766543962415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298562586813060088234466213 55980485027448766543962415)
    ·
      refine ⟨83970727541173149815943623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55980485027448766543962415 83970727541173149815943623)
      ·
        refine ⟨125956091311759724723915435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83970727541173149815943623 125956091311759724723915435)
        ·
          refine ⟨188934136967639587085873153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125956091311759724723915435 188934136967639587085873153)
          ·
            refine ⟨141700602725729690314404865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188934136967639587085873153 141700602725729690314404865)
            ·
              refine ⟨106275452044297267735803649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141700602725729690314404865 106275452044297267735803649)
              ·
                refine ⟨79706589033222950801852737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106275452044297267735803649 79706589033222950801852737)
                ·
                  refine ⟨59779941774917213101389553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79706589033222950801852737 59779941774917213101389553)
                  ·
                    refine ⟨44834956331187909826042165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59779941774917213101389553 44834956331187909826042165)
                    ·
                      refine ⟨4203277156048866546191453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44834956331187909826042165 4203277156048866546191453)
                      ·
                        rfl

theorem cell23_8185853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_8185853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185853 prefixEnd_8185853 := by exact prefixLift 8185853
  have htrace : WordTrace (prefixWord ++ tailWord_8185853) baseStart_8185853 baseEnd_8185853 := by
    simpa [prefixWord, tailWord_8185853, baseEnd_8185853] using wordTrace_append hprefix tailTrace_8185853
  have hstable : (prefixWord ++ tailWord_8185853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185853).length < 2 ^ (prefixWord ++ tailWord_8185853).sum := by decide
  have hdescent : baseEnd_8185853 < baseStart_8185853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185883 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 5]
def baseStart_8185883 : Nat := 118140960795 + 8185883 * 2 ^ 59
def prefixEnd_8185883 : Nat := 4983230072969 + 3 ^ 40 * 8185883 * 2
def baseEnd_8185883 : Nat := 4203292560468501428816315

theorem tailTrace_8185883 : CollatzResearch.WordTrace tailWord_8185883 prefixEnd_8185883 4203292560468501428816315 := by
  unfold tailWord_8185883
  simp only [CollatzResearch.WordTrace]
  refine ⟨298563681002951403358058303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199042454001967602238705535 298563681002951403358058303)
  ·
    refine ⟨447845521504427105037087455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298563681002951403358058303 447845521504427105037087455)
    ·
      refine ⟨671768282256640657555631183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447845521504427105037087455 671768282256640657555631183)
      ·
        refine ⟨1007652423384960986333446775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671768282256640657555631183 1007652423384960986333446775)
        ·
          refine ⟨1511478635077441479500170163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007652423384960986333446775 1511478635077441479500170163)
          ·
            refine ⟨2267217952616162219250255245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511478635077441479500170163 2267217952616162219250255245)
            ·
              refine ⟨850206732231060832218845717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2267217952616162219250255245 850206732231060832218845717)
              ·
                refine ⟨39853440573330976510258393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 850206732231060832218845717 39853440573330976510258393)
                ·
                  refine ⟨29890080429998232382693795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39853440573330976510258393 29890080429998232382693795)
                  ·
                    refine ⟨44835120644997348574040693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29890080429998232382693795 44835120644997348574040693)
                    ·
                      refine ⟨4203292560468501428816315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44835120644997348574040693 4203292560468501428816315)
                      ·
                        rfl

theorem cell23_8185883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 5].length) (baseStart_8185883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185883 prefixEnd_8185883 := by exact prefixLift 8185883
  have htrace : WordTrace (prefixWord ++ tailWord_8185883) baseStart_8185883 baseEnd_8185883 := by
    simpa [prefixWord, tailWord_8185883, baseEnd_8185883] using wordTrace_append hprefix tailTrace_8185883
  have hstable : (prefixWord ++ tailWord_8185883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185883).length < 2 ^ (prefixWord ++ tailWord_8185883).sum := by decide
  have hdescent : baseEnd_8185883 < baseStart_8185883 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185908 : List Nat := [2, 5, 1, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_8185908 : Nat := 118140960795 + 8185908 * 2 ^ 59
def prefixEnd_8185908 : Nat := 4983230072969 + 3 ^ 40 * 8185908 * 2
def baseEnd_8185908 : Nat := 4203305397484863831003701

theorem tailTrace_8185908 : CollatzResearch.WordTrace tailWord_8185908 prefixEnd_8185908 4203305397484863831003701 := by
  unfold tailWord_8185908
  simp only [CollatzResearch.WordTrace]
  refine ⟨149282296413930416313859189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199043061885240555085145585 149282296413930416313859189)
  ·
    refine ⟨13995215288805976529424299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149282296413930416313859189 13995215288805976529424299)
    ·
      refine ⟨20992822933208964794136449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13995215288805976529424299 20992822933208964794136449)
      ·
        refine ⟨15744617199906723595602337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20992822933208964794136449 15744617199906723595602337)
        ·
          refine ⟨11808462899930042696701753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15744617199906723595602337 11808462899930042696701753)
          ·
            refine ⟨8856347174947532022526315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11808462899930042696701753 8856347174947532022526315)
            ·
              refine ⟨13284520762421298033789473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8856347174947532022526315 13284520762421298033789473)
              ·
                refine ⟨9963390571815973525342105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13284520762421298033789473 9963390571815973525342105)
                ·
                  refine ⟨7472542928861980144006579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9963390571815973525342105 7472542928861980144006579)
                  ·
                    refine ⟨11208814393292970216009869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7472542928861980144006579 11208814393292970216009869)
                    ·
                      refine ⟨4203305397484863831003701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11208814393292970216009869 4203305397484863831003701)
                      ·
                        rfl

theorem cell23_8185908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_8185908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185908 prefixEnd_8185908 := by exact prefixLift 8185908
  have htrace : WordTrace (prefixWord ++ tailWord_8185908) baseStart_8185908 baseEnd_8185908 := by
    simpa [prefixWord, tailWord_8185908, baseEnd_8185908] using wordTrace_append hprefix tailTrace_8185908
  have hstable : (prefixWord ++ tailWord_8185908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185908).length < 2 ^ (prefixWord ++ tailWord_8185908).sum := by decide
  have hdescent : baseEnd_8185908 < baseStart_8185908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8185920 : List Nat := [2, 1, 1, 2, 2, 5, 2, 1, 7]
def baseStart_8185920 : Nat := 118140960795 + 8185920 * 2 ^ 59
def prefixEnd_8185920 : Nat := 4983230072969 + 3 ^ 40 * 8185920 * 2
def baseEnd_8185920 : Nat := 467034617694746420450405

theorem tailTrace_8185920 : CollatzResearch.WordTrace tailWord_8185920 prefixEnd_8185920 467034617694746420450405 := by
  unfold tailWord_8185920
  simp only [CollatzResearch.WordTrace]
  refine ⟨149282515251908679338577607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199043353669211572451436809 149282515251908679338577607)
  ·
    refine ⟨223923772877863019007866411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149282515251908679338577607 223923772877863019007866411)
    ·
      refine ⟨335885659316794528511799617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223923772877863019007866411 335885659316794528511799617)
      ·
        refine ⟨251914244487595896383849713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335885659316794528511799617 251914244487595896383849713)
        ·
          refine ⟨188935683365696922287887285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251914244487595896383849713 188935683365696922287887285)
          ·
            refine ⟨17712720315534086464489433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188935683365696922287887285 17712720315534086464489433)
            ·
              refine ⟨13284540236650564848367075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17712720315534086464489433 13284540236650564848367075)
              ·
                refine ⟨19926810354975847272550613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13284540236650564848367075 19926810354975847272550613)
                ·
                  refine ⟨467034617694746420450405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19926810354975847272550613 467034617694746420450405)
                  ·
                    rfl

theorem cell23_8185920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 7].length) (baseStart_8185920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8185920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8185920 prefixEnd_8185920 := by exact prefixLift 8185920
  have htrace : WordTrace (prefixWord ++ tailWord_8185920) baseStart_8185920 baseEnd_8185920 := by
    simpa [prefixWord, tailWord_8185920, baseEnd_8185920] using wordTrace_append hprefix tailTrace_8185920
  have hstable : (prefixWord ++ tailWord_8185920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8185920).length < 2 ^ (prefixWord ++ tailWord_8185920).sum := by decide
  have hdescent : baseEnd_8185920 < baseStart_8185920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8185920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186040 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 5, 5]
def baseStart_8186040 : Nat := 118140960795 + 8186040 * 2 ^ 59
def prefixEnd_8186040 : Nat := 4983230072969 + 3 ^ 40 * 8186040 * 2
def baseEnd_8186040 : Nat := 1401124392310419104851031

theorem tailTrace_8186040 : CollatzResearch.WordTrace tailWord_8186040 prefixEnd_8186040 1401124392310419104851031 := by
  unfold tailWord_8186040
  simp only [CollatzResearch.WordTrace]
  refine ⟨149284703631691309585761787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199046271508921746114349049 149284703631691309585761787)
  ·
    refine ⟨223927055447536964378642681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149284703631691309585761787 223927055447536964378642681)
    ·
      refine ⟨167945291585652723283982011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223927055447536964378642681 167945291585652723283982011)
      ·
        refine ⟨251917937378479084925973017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167945291585652723283982011 251917937378479084925973017)
        ·
          refine ⟨188938453033859313694479763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251917937378479084925973017 188938453033859313694479763)
          ·
            refine ⟨283407679550788970541719645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188938453033859313694479763 283407679550788970541719645)
            ·
              refine ⟨106277879831545863953144867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283407679550788970541719645 106277879831545863953144867)
              ·
                refine ⟨159416819747318795929717301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106277879831545863953144867 159416819747318795929717301)
                ·
                  refine ⟨14945326851311137118410997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159416819747318795929717301 14945326851311137118410997)
                  ·
                    refine ⟨1401124392310419104851031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14945326851311137118410997 1401124392310419104851031)
                    ·
                      rfl

theorem cell23_8186040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_8186040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186040 prefixEnd_8186040 := by exact prefixLift 8186040
  have htrace : WordTrace (prefixWord ++ tailWord_8186040) baseStart_8186040 baseEnd_8186040 := by
    simpa [prefixWord, tailWord_8186040, baseEnd_8186040] using wordTrace_append hprefix tailTrace_8186040
  have hstable : (prefixWord ++ tailWord_8186040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186040).length < 2 ^ (prefixWord ++ tailWord_8186040).sum := by decide
  have hdescent : baseEnd_8186040 < baseStart_8186040 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186047 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 1, 5, 2]
def baseStart_8186047 : Nat := 118140960795 + 8186047 * 2 ^ 59
def prefixEnd_8186047 : Nat := 4983230072969 + 3 ^ 40 * 8186047 * 2
def baseEnd_8186047 : Nat := 4203376771295838787165561

theorem tailTrace_8186047 : CollatzResearch.WordTrace tailWord_8186047 prefixEnd_8186047 4203376771295838787165561 := by
  unfold tailWord_8186047
  simp only [CollatzResearch.WordTrace]
  refine ⟨298569662574357259367028395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199046441716238172911352263 298569662574357259367028395)
  ·
    refine ⟨447854493861535889050542593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298569662574357259367028395 447854493861535889050542593)
    ·
      refine ⟨335890870396151916787906945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447854493861535889050542593 335890870396151916787906945)
      ·
        refine ⟨251918152797113937590930209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335890870396151916787906945 251918152797113937590930209)
        ·
          refine ⟨188938614597835453193197657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251918152797113937590930209 188938614597835453193197657)
          ·
            refine ⟨141703960948376589894898243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188938614597835453193197657 141703960948376589894898243)
            ·
              refine ⟨212555941422564884842347365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141703960948376589894898243 212555941422564884842347365)
              ·
                refine ⟨39854239016730915907940131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212555941422564884842347365 39854239016730915907940131)
                ·
                  refine ⟨59781358525096373861910197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39854239016730915907940131 59781358525096373861910197)
                  ·
                    refine ⟨5604502361727785049554081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59781358525096373861910197 5604502361727785049554081)
                    ·
                      refine ⟨4203376771295838787165561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5604502361727785049554081 4203376771295838787165561)
                      ·
                        rfl

theorem cell23_8186047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 5, 2].length) (baseStart_8186047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186047 prefixEnd_8186047 := by exact prefixLift 8186047
  have htrace : WordTrace (prefixWord ++ tailWord_8186047) baseStart_8186047 baseEnd_8186047 := by
    simpa [prefixWord, tailWord_8186047, baseEnd_8186047] using wordTrace_append hprefix tailTrace_8186047
  have hstable : (prefixWord ++ tailWord_8186047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186047).length < 2 ^ (prefixWord ++ tailWord_8186047).sum := by decide
  have hdescent : baseEnd_8186047 < baseStart_8186047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186074 : List Nat := [3, 1, 1, 2, 2, 1, 6, 1, 1, 5]
def baseStart_8186074 : Nat := 118140960795 + 8186074 * 2 ^ 59
def prefixEnd_8186074 : Nat := 4983230072969 + 3 ^ 40 * 8186074 * 2
def baseEnd_8186074 : Nat := 1401130211757836727175979

theorem tailTrace_8186074 : CollatzResearch.WordTrace tailWord_8186074 prefixEnd_8186074 1401130211757836727175979 := by
  unfold tailWord_8186074
  simp only [CollatzResearch.WordTrace]
  refine ⟨74642661836314860744565319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199047098230172961985507517 74642661836314860744565319)
  ·
    refine ⟨111963992754472291116847979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74642661836314860744565319 111963992754472291116847979)
    ·
      refine ⟨167945989131708436675271969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111963992754472291116847979 167945989131708436675271969)
      ·
        refine ⟨125959491848781327506453977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167945989131708436675271969 125959491848781327506453977)
        ·
          refine ⟨94469618886585995629840483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125959491848781327506453977 94469618886585995629840483)
          ·
            refine ⟨141704428329878993444760725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94469618886585995629840483 141704428329878993444760725)
            ·
              refine ⟨6642395077963077817723159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141704428329878993444760725 6642395077963077817723159)
              ·
                refine ⟨9963592616944616726584739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6642395077963077817723159 9963592616944616726584739)
                ·
                  refine ⟨14945388925416925089877109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9963592616944616726584739 14945388925416925089877109)
                  ·
                    refine ⟨1401130211757836727175979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14945388925416925089877109 1401130211757836727175979)
                    ·
                      rfl

theorem cell23_8186074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_8186074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186074 prefixEnd_8186074 := by exact prefixLift 8186074
  have htrace : WordTrace (prefixWord ++ tailWord_8186074) baseStart_8186074 baseEnd_8186074 := by
    simpa [prefixWord, tailWord_8186074, baseEnd_8186074] using wordTrace_append hprefix tailTrace_8186074
  have hstable : (prefixWord ++ tailWord_8186074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186074).length < 2 ^ (prefixWord ++ tailWord_8186074).sum := by decide
  have hdescent : baseEnd_8186074 < baseStart_8186074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186097 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 5, 2, 3]
def baseStart_8186097 : Nat := 118140960795 + 8186097 * 2 ^ 59
def prefixEnd_8186097 : Nat := 4983230072969 + 3 ^ 40 * 8186097 * 2
def baseEnd_8186097 : Nat := 4203402445328563591540331

theorem tailTrace_8186097 : CollatzResearch.WordTrace tailWord_8186097 prefixEnd_8186097 4203402445328563591540331 := by
  unfold tailWord_8186097
  simp only [CollatzResearch.WordTrace]
  refine ⟨298571486224176117906348545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199047657482784078604232363 298571486224176117906348545)
  ·
    refine ⟨223928614668132088429761409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298571486224176117906348545 223928614668132088429761409)
    ·
      refine ⟨167946461001099066322321057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223928614668132088429761409 167946461001099066322321057)
      ·
        refine ⟨125959845750824299741740793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167946461001099066322321057 125959845750824299741740793)
        ·
          refine ⟨94469884313118224806305595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125959845750824299741740793 94469884313118224806305595)
          ·
            refine ⟨141704826469677337209458393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94469884313118224806305595 141704826469677337209458393)
            ·
              refine ⟨106278619852258002907093795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141704826469677337209458393 106278619852258002907093795)
              ·
                refine ⟨159417929778387004360640693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106278619852258002907093795 159417929778387004360640693)
                ·
                  refine ⟨14945430916723781658810065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159417929778387004360640693 14945430916723781658810065)
                  ·
                    refine ⟨11209073187542836244107549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14945430916723781658810065 11209073187542836244107549)
                    ·
                      refine ⟨4203402445328563591540331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11209073187542836244107549 4203402445328563591540331)
                      ·
                        rfl

theorem cell23_8186097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_8186097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186097 prefixEnd_8186097 := by exact prefixLift 8186097
  have htrace : WordTrace (prefixWord ++ tailWord_8186097) baseStart_8186097 baseEnd_8186097 := by
    simpa [prefixWord, tailWord_8186097, baseEnd_8186097] using wordTrace_append hprefix tailTrace_8186097
  have hstable : (prefixWord ++ tailWord_8186097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186097).length < 2 ^ (prefixWord ++ tailWord_8186097).sum := by decide
  have hdescent : baseEnd_8186097 < baseStart_8186097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186127 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 3]
def baseStart_8186127 : Nat := 118140960795 + 8186127 * 2 ^ 59
def prefixEnd_8186127 : Nat := 4983230072969 + 3 ^ 40 * 8186127 * 2
def baseEnd_8186127 : Nat := 4203417849748198474165193

theorem tailTrace_8186127 : CollatzResearch.WordTrace tailWord_8186127 prefixEnd_8186127 4203417849748198474165193 := by
  unfold tailWord_8186127
  simp only [CollatzResearch.WordTrace]
  refine ⟨298572580414067433029940635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199048386942711622019960423 298572580414067433029940635)
  ·
    refine ⟨447858870621101149544910953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298572580414067433029940635 447858870621101149544910953)
    ·
      refine ⟨335894152965825862158683215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447858870621101149544910953 335894152965825862158683215)
      ·
        refine ⟨503841229448738793238024823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335894152965825862158683215 503841229448738793238024823)
        ·
          refine ⟨755761844173108189857037235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503841229448738793238024823 755761844173108189857037235)
          ·
            refine ⟨1133642766259662284785555853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 755761844173108189857037235 1133642766259662284785555853)
            ·
              refine ⟨425116037347373356794583445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1133642766259662284785555853 425116037347373356794583445)
              ·
                refine ⟨19927314250658126099746099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 425116037347373356794583445 19927314250658126099746099)
                ·
                  refine ⟨29890971375987189149619149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19927314250658126099746099 29890971375987189149619149)
                  ·
                    refine ⟨11209114265995195931107181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29890971375987189149619149 11209114265995195931107181)
                    ·
                      refine ⟨4203417849748198474165193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11209114265995195931107181 4203417849748198474165193)
                      ·
                        rfl

theorem cell23_8186127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 3].length) (baseStart_8186127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186127 prefixEnd_8186127 := by exact prefixLift 8186127
  have htrace : WordTrace (prefixWord ++ tailWord_8186127) baseStart_8186127 baseEnd_8186127 := by
    simpa [prefixWord, tailWord_8186127, baseEnd_8186127] using wordTrace_append hprefix tailTrace_8186127
  have hstable : (prefixWord ++ tailWord_8186127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186127).length < 2 ^ (prefixWord ++ tailWord_8186127).sum := by decide
  have hdescent : baseEnd_8186127 < baseStart_8186127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186184 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 3, 4, 2]
def baseStart_8186184 : Nat := 118140960795 + 8186184 * 2 ^ 59
def prefixEnd_8186184 : Nat := 4983230072969 + 3 ^ 40 * 8186184 * 2
def baseEnd_8186184 : Nat := 4203447118145504751152431

theorem tailTrace_8186184 : CollatzResearch.WordTrace tailWord_8186184 prefixEnd_8186184 4203447118145504751152431 := by
  unfold tailWord_8186184
  simp only [CollatzResearch.WordTrace]
  refine ⟨149287329687430465882382803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199049772916573954509843737 149287329687430465882382803)
  ·
    refine ⟨223930994531145698823574205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149287329687430465882382803 223930994531145698823574205)
    ·
      refine ⟨83974122949179637058840327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223930994531145698823574205 83974122949179637058840327)
      ·
        refine ⟨125961184423769455588260491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83974122949179637058840327 125961184423769455588260491)
        ·
          refine ⟨188941776635654183382390737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125961184423769455588260491 188941776635654183382390737)
          ·
            refine ⟨141706332476740637536793053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188941776635654183382390737 141706332476740637536793053)
            ·
              refine ⟨53139874678777739076297395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141706332476740637536793053 53139874678777739076297395)
              ·
                refine ⟨79709812018166608614446093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53139874678777739076297395 79709812018166608614446093)
                ·
                  refine ⟨29891179506812478230417285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79709812018166608614446093 29891179506812478230417285)
                  ·
                    refine ⟨5604596157527339668203241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29891179506812478230417285 5604596157527339668203241)
                    ·
                      refine ⟨4203447118145504751152431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5604596157527339668203241 4203447118145504751152431)
                      ·
                        rfl

theorem cell23_8186184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_8186184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186184 prefixEnd_8186184 := by exact prefixLift 8186184
  have htrace : WordTrace (prefixWord ++ tailWord_8186184) baseStart_8186184 baseEnd_8186184 := by
    simpa [prefixWord, tailWord_8186184, baseEnd_8186184] using wordTrace_append hprefix tailTrace_8186184
  have hstable : (prefixWord ++ tailWord_8186184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186184).length < 2 ^ (prefixWord ++ tailWord_8186184).sum := by decide
  have hdescent : baseEnd_8186184 < baseStart_8186184 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186188 : List Nat := [2, 2, 1, 3, 2, 1, 5, 1, 1, 3, 2]
def baseStart_8186188 : Nat := 118140960795 + 8186188 * 2 ^ 59
def prefixEnd_8186188 : Nat := 4983230072969 + 3 ^ 40 * 8186188 * 2
def baseEnd_8186188 : Nat := 4203449172068122735502413

theorem tailTrace_8186188 : CollatzResearch.WordTrace tailWord_8186188 prefixEnd_8186188 4203449172068122735502413 := by
  unfold tailWord_8186188
  simp only [CollatzResearch.WordTrace]
  refine ⟨149287402633423220223955609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199049870177897626965274145 149287402633423220223955609)
  ·
    refine ⟨111965551975067415167966707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149287402633423220223955609 111965551975067415167966707)
    ·
      refine ⟨167948327962601122751950061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111965551975067415167966707 167948327962601122751950061)
      ·
        refine ⟨62980622985975421031981273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167948327962601122751950061 62980622985975421031981273)
        ·
          refine ⟨47235467239481565773985955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62980622985975421031981273 47235467239481565773985955)
          ·
            refine ⟨70853200859222348660978933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47235467239481565773985955 70853200859222348660978933)
            ·
              refine ⟨6642487580552095186966775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70853200859222348660978933 6642487580552095186966775)
              ·
                refine ⟨9963731370828142780450163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6642487580552095186966775 9963731370828142780450163)
                ·
                  refine ⟨14945597056242214170675245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9963731370828142780450163 14945597056242214170675245)
                  ·
                    refine ⟨5604598896090830314003217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14945597056242214170675245 5604598896090830314003217)
                    ·
                      refine ⟨4203449172068122735502413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5604598896090830314003217 4203449172068122735502413)
                      ·
                        rfl

theorem cell23_8186188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_8186188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186188 prefixEnd_8186188 := by exact prefixLift 8186188
  have htrace : WordTrace (prefixWord ++ tailWord_8186188) baseStart_8186188 baseEnd_8186188 := by
    simpa [prefixWord, tailWord_8186188, baseEnd_8186188] using wordTrace_append hprefix tailTrace_8186188
  have hstable : (prefixWord ++ tailWord_8186188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186188).length < 2 ^ (prefixWord ++ tailWord_8186188).sum := by decide
  have hdescent : baseEnd_8186188 < baseStart_8186188 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186218 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_8186218 : Nat := 118140960795 + 8186218 * 2 ^ 59
def prefixEnd_8186218 : Nat := 4983230072969 + 3 ^ 40 * 8186218 * 2
def baseEnd_8186218 : Nat := 4203464576487757618127275

theorem tailTrace_8186218 : CollatzResearch.WordTrace tailWord_8186218 prefixEnd_8186218 4203464576487757618127275 := by
  unfold tailWord_8186218
  simp only [CollatzResearch.WordTrace]
  refine ⟨74643974864184438892875827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199050599637825170381002205 74643974864184438892875827)
  ·
    refine ⟨111965962296276658339313741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74643974864184438892875827 111965962296276658339313741)
    ·
      refine ⟨41987235861103746877242653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111965962296276658339313741 41987235861103746877242653)
      ·
        refine ⟨15745213447913905078965995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41987235861103746877242653 15745213447913905078965995)
        ·
          refine ⟨23617820171870857618448993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15745213447913905078965995 23617820171870857618448993)
          ·
            refine ⟨17713365128903143213836745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23617820171870857618448993 17713365128903143213836745)
            ·
              refine ⟨13285023846677357410377559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17713365128903143213836745 13285023846677357410377559)
              ·
                refine ⟨19927535770016036115566339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13285023846677357410377559 19927535770016036115566339)
                ·
                  refine ⟨29891303655024054173349509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19927535770016036115566339 29891303655024054173349509)
                  ·
                    refine ⟨5604619435317010157503033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29891303655024054173349509 5604619435317010157503033)
                    ·
                      refine ⟨4203464576487757618127275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5604619435317010157503033 4203464576487757618127275)
                      ·
                        rfl

theorem cell23_8186218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_8186218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186218 prefixEnd_8186218 := by exact prefixLift 8186218
  have htrace : WordTrace (prefixWord ++ tailWord_8186218) baseStart_8186218 baseEnd_8186218 := by
    simpa [prefixWord, tailWord_8186218, baseEnd_8186218] using wordTrace_append hprefix tailTrace_8186218
  have hstable : (prefixWord ++ tailWord_8186218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186218).length < 2 ^ (prefixWord ++ tailWord_8186218).sum := by decide
  have hdescent : baseEnd_8186218 < baseStart_8186218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186241 : List Nat := [1, 2, 4, 3, 1, 1, 1, 5, 5]
def baseStart_8186241 : Nat := 118140960795 + 8186241 * 2 ^ 59
def prefixEnd_8186241 : Nat := 4983230072969 + 3 ^ 40 * 8186241 * 2
def baseEnd_8186241 : Nat := 467052931838090114237741

theorem tailTrace_8186241 : CollatzResearch.WordTrace tailWord_8186241 prefixEnd_8186241 467052931838090114237741 := by
  unfold tailWord_8186241
  simp only [CollatzResearch.WordTrace]
  refine ⟨298576738335654430499590577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199051158890436286999727051 298576738335654430499590577)
  ·
    refine ⟨223932553751740822874692933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298576738335654430499590577 223932553751740822874692933)
    ·
      refine ⟨41987353828451404289004925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223932553751740822874692933 41987353828451404289004925)
      ·
        refine ⟨15745257685669276608376847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41987353828451404289004925 15745257685669276608376847)
        ·
          refine ⟨23617886528503914912565271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15745257685669276608376847 23617886528503914912565271)
          ·
            refine ⟨35426829792755872368847907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23617886528503914912565271 35426829792755872368847907)
            ·
              refine ⟨53140244689133808553271861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35426829792755872368847907 53140244689133808553271861)
              ·
                refine ⟨4981897939606294551869237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53140244689133808553271861 4981897939606294551869237)
                ·
                  refine ⟨467052931838090114237741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4981897939606294551869237 467052931838090114237741)
                  ·
                    rfl

theorem cell23_8186241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 5].length) (baseStart_8186241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186241 prefixEnd_8186241 := by exact prefixLift 8186241
  have htrace : WordTrace (prefixWord ++ tailWord_8186241) baseStart_8186241 baseEnd_8186241 := by
    simpa [prefixWord, tailWord_8186241, baseEnd_8186241] using wordTrace_append hprefix tailTrace_8186241
  have hstable : (prefixWord ++ tailWord_8186241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186241).length < 2 ^ (prefixWord ++ tailWord_8186241).sum := by decide
  have hdescent : baseEnd_8186241 < baseStart_8186241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186257 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_8186257 : Nat := 118140960795 + 8186257 * 2 ^ 59
def prefixEnd_8186257 : Nat := 4983230072969 + 3 ^ 40 * 8186257 * 2
def baseEnd_8186257 : Nat := 4203484602233282965539595

theorem tailTrace_8186257 : CollatzResearch.WordTrace tailWord_8186257 prefixEnd_8186257 4203484602233282965539595 := by
  unfold tailWord_8186257
  simp only [CollatzResearch.WordTrace]
  refine ⟨298577321903596465232173025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199051547935730976821448683 298577321903596465232173025)
  ·
    refine ⟨223932991427697348924129769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298577321903596465232173025 223932991427697348924129769)
    ·
      refine ⟨167949743570773011693097327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223932991427697348924129769 167949743570773011693097327)
      ·
        refine ⟨251924615356159517539645991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167949743570773011693097327 251924615356159517539645991)
        ·
          refine ⟨377886923034239276309468987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251924615356159517539645991 377886923034239276309468987)
          ·
            refine ⟨566830384551358914464203481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377886923034239276309468987 566830384551358914464203481)
            ·
              refine ⟨425122788413519185848152611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566830384551358914464203481 425122788413519185848152611)
              ·
                refine ⟨637684182620278778772228917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425122788413519185848152611 637684182620278778772228917)
                ·
                  refine ⟨59782892120651135509896461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 637684182620278778772228917 59782892120651135509896461)
                  ·
                    refine ⟨22418584545244175816211173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59782892120651135509896461 22418584545244175816211173)
                    ·
                      refine ⟨4203484602233282965539595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22418584545244175816211173 4203484602233282965539595)
                      ·
                        rfl

theorem cell23_8186257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_8186257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186257 prefixEnd_8186257 := by exact prefixLift 8186257
  have htrace : WordTrace (prefixWord ++ tailWord_8186257) baseStart_8186257 baseEnd_8186257 := by
    simpa [prefixWord, tailWord_8186257, baseEnd_8186257] using wordTrace_append hprefix tailTrace_8186257
  have hstable : (prefixWord ++ tailWord_8186257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186257).length < 2 ^ (prefixWord ++ tailWord_8186257).sum := by decide
  have hdescent : baseEnd_8186257 < baseStart_8186257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186274 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_8186274 : Nat := 118140960795 + 8186274 * 2 ^ 59
def prefixEnd_8186274 : Nat := 4983230072969 + 3 ^ 40 * 8186274 * 2
def baseEnd_8186274 : Nat := 4203493331404409399027017

theorem tailTrace_8186274 : CollatzResearch.WordTrace tailWord_8186274 prefixEnd_8186274 4203493331404409399027017 := by
  unfold tailWord_8186274
  simp only [CollatzResearch.WordTrace]
  refine ⟨74644485486133719283885469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199051961296356584757027917 74644485486133719283885469)
  ·
    refine ⟨27991682057300144731457051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74644485486133719283885469 27991682057300144731457051)
    ·
      refine ⟨41987523085950217097185577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27991682057300144731457051 41987523085950217097185577)
      ·
        refine ⟨31490642314462662822889183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41987523085950217097185577 31490642314462662822889183)
        ·
          refine ⟨47235963471693994234333775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31490642314462662822889183 47235963471693994234333775)
          ·
            refine ⟨70853945207540991351500663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47235963471693994234333775 70853945207540991351500663)
            ·
              refine ⟨106280917811311487027250995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70853945207540991351500663 106280917811311487027250995)
              ·
                refine ⟨159421376716967230540876493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106280917811311487027250995 159421376716967230540876493)
                ·
                  refine ⟨59783016268862711452828685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159421376716967230540876493 59783016268862711452828685)
                  ·
                    refine ⟨22418631100823516794810757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59783016268862711452828685 22418631100823516794810757)
                    ·
                      refine ⟨4203493331404409399027017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22418631100823516794810757 4203493331404409399027017)
                      ·
                        rfl

theorem cell23_8186274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_8186274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186274 prefixEnd_8186274 := by exact prefixLift 8186274
  have htrace : WordTrace (prefixWord ++ tailWord_8186274) baseStart_8186274 baseEnd_8186274 := by
    simpa [prefixWord, tailWord_8186274, baseEnd_8186274] using wordTrace_append hprefix tailTrace_8186274
  have hstable : (prefixWord ++ tailWord_8186274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186274).length < 2 ^ (prefixWord ++ tailWord_8186274).sum := by decide
  have hdescent : baseEnd_8186274 < baseStart_8186274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186292 : List Nat := [2, 5, 2, 2, 1, 2, 1, 3, 5]
def baseStart_8186292 : Nat := 118140960795 + 8186292 * 2 ^ 59
def prefixEnd_8186292 : Nat := 4983230072969 + 3 ^ 40 * 8186292 * 2
def baseEnd_8186292 : Nat := 467055841561798925400215

theorem tailTrace_8186292 : CollatzResearch.WordTrace tailWord_8186292 prefixEnd_8186292 467055841561798925400215 := by
  unfold tailWord_8186292
  simp only [CollatzResearch.WordTrace]
  refine ⟨149289299229234833104848565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199052398972313110806464753 149289299229234833104848565)
  ·
    refine ⟨13995871802740765603579553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149289299229234833104848565 13995871802740765603579553)
    ·
      refine ⟨10496903852055574202684665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13995871802740765603579553 10496903852055574202684665)
      ·
        refine ⟨7872677889041680652013499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10496903852055574202684665 7872677889041680652013499)
        ·
          refine ⟨11809016833562520978020249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872677889041680652013499 11809016833562520978020249)
          ·
            refine ⟨8856762625171890733515187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11809016833562520978020249 8856762625171890733515187)
            ·
              refine ⟨13285143937757836100272781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8856762625171890733515187 13285143937757836100272781)
              ·
                refine ⟨4981928976659188537602293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13285143937757836100272781 4981928976659188537602293)
                ·
                  refine ⟨467055841561798925400215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4981928976659188537602293 467055841561798925400215)
                  ·
                    rfl

theorem cell23_8186292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_8186292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186292 prefixEnd_8186292 := by exact prefixLift 8186292
  have htrace : WordTrace (prefixWord ++ tailWord_8186292) baseStart_8186292 baseEnd_8186292 := by
    simpa [prefixWord, tailWord_8186292, baseEnd_8186292] using wordTrace_append hprefix tailTrace_8186292
  have hstable : (prefixWord ++ tailWord_8186292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186292).length < 2 ^ (prefixWord ++ tailWord_8186292).sum := by decide
  have hdescent : baseEnd_8186292 < baseStart_8186292 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186305 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 2, 5]
def baseStart_8186305 : Nat := 118140960795 + 8186305 * 2 ^ 59
def prefixEnd_8186305 : Nat := 4983230072969 + 3 ^ 40 * 8186305 * 2
def baseEnd_8186305 : Nat := 1401169749768232925913125

theorem tailTrace_8186305 : CollatzResearch.WordTrace tailWord_8186305 prefixEnd_8186305 1401169749768232925913125 := by
  unfold tailWord_8186305
  simp only [CollatzResearch.WordTrace]
  refine ⟨298579072607422569429920369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199052715071615046286613579 298579072607422569429920369)
  ·
    refine ⟨223934304455566927072440277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298579072607422569429920369 223934304455566927072440277)
    ·
      refine ⟨5248460260677349853260319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 223934304455566927072440277 5248460260677349853260319)
      ·
        refine ⟨7872690391016024779890479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248460260677349853260319 7872690391016024779890479)
        ·
          refine ⟨11809035586524037169835719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872690391016024779890479 11809035586524037169835719)
          ·
            refine ⟨17713553379786055754753579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11809035586524037169835719 17713553379786055754753579)
            ·
              refine ⟨26570330069679083632130369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17713553379786055754753579 26570330069679083632130369)
              ·
                refine ⟨19927747552259312724097777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26570330069679083632130369 19927747552259312724097777)
                ·
                  refine ⟨14945810664194484543073333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19927747552259312724097777 14945810664194484543073333)
                  ·
                    refine ⟨1401169749768232925913125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14945810664194484543073333 1401169749768232925913125)
                    ·
                      rfl

theorem cell23_8186305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_8186305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186305 prefixEnd_8186305 := by exact prefixLift 8186305
  have htrace : WordTrace (prefixWord ++ tailWord_8186305) baseStart_8186305 baseEnd_8186305 := by
    simpa [prefixWord, tailWord_8186305, baseEnd_8186305] using wordTrace_append hprefix tailTrace_8186305
  have hstable : (prefixWord ++ tailWord_8186305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186305).length < 2 ^ (prefixWord ++ tailWord_8186305).sum := by decide
  have hdescent : baseEnd_8186305 < baseStart_8186305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186308 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_8186308 : Nat := 118140960795 + 8186308 * 2 ^ 59
def prefixEnd_8186308 : Nat := 4983230072969 + 3 ^ 40 * 8186308 * 2
def baseEnd_8186308 : Nat := 4203510789746662266001861

theorem tailTrace_8186308 : CollatzResearch.WordTrace tailWord_8186308 prefixEnd_8186308 4203510789746662266001861 := by
  unfold tailWord_8186308
  simp only [CollatzResearch.WordTrace]
  refine ⟨149289591013205850471139789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199052788017607800628186385 149289591013205850471139789)
  ·
    refine ⟨55983596629952193926677421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149289591013205850471139789 55983596629952193926677421)
    ·
      refine ⟨20993848736232072722504033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55983596629952193926677421 20993848736232072722504033)
      ·
        refine ⟨15745386552174054541878025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20993848736232072722504033 15745386552174054541878025)
        ·
          refine ⟨11809039914130540906408519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15745386552174054541878025 11809039914130540906408519)
          ·
            refine ⟨17713559871195811359612779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11809039914130540906408519 17713559871195811359612779)
            ·
              refine ⟨26570339806793717039419169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17713559871195811359612779 26570339806793717039419169)
              ·
                refine ⟨19927754855095287779564377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26570339806793717039419169 19927754855095287779564377)
                ·
                  refine ⟨14945816141321465834673283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19927754855095287779564377 14945816141321465834673283)
                  ·
                    refine ⟨22418724211982198752009925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14945816141321465834673283 22418724211982198752009925)
                    ·
                      refine ⟨4203510789746662266001861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22418724211982198752009925 4203510789746662266001861)
                      ·
                        rfl

theorem cell23_8186308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_8186308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186308 prefixEnd_8186308 := by exact prefixLift 8186308
  have htrace : WordTrace (prefixWord ++ tailWord_8186308) baseStart_8186308 baseEnd_8186308 := by
    simpa [prefixWord, tailWord_8186308, baseEnd_8186308] using wordTrace_append hprefix tailTrace_8186308
  have hstable : (prefixWord ++ tailWord_8186308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186308).length < 2 ^ (prefixWord ++ tailWord_8186308).sum := by decide
  have hdescent : baseEnd_8186308 < baseStart_8186308 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186311 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_8186311 : Nat := 118140960795 + 8186311 * 2 ^ 59
def prefixEnd_8186311 : Nat := 4983230072969 + 3 ^ 40 * 8186311 * 2
def baseEnd_8186311 : Nat := 4203512330188625754264347

theorem tailTrace_8186311 : CollatzResearch.WordTrace tailWord_8186311 prefixEnd_8186311 4203512330188625754264347 := by
  unfold tailWord_8186311
  simp only [CollatzResearch.WordTrace]
  refine ⟨298579291445400832454638787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199052860963600554969759191 298579291445400832454638787)
  ·
    refine ⟨447868937168101248681958181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298579291445400832454638787 447868937168101248681958181)
    ·
      refine ⟨83975425719018984127867159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447868937168101248681958181 83975425719018984127867159)
      ·
        refine ⟨125963138578528476191800739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83975425719018984127867159 125963138578528476191800739)
        ·
          refine ⟨188944707867792714287701109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125963138578528476191800739 188944707867792714287701109)
          ·
            refine ⟨17713566362605566964471979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188944707867792714287701109 17713566362605566964471979)
            ·
              refine ⟨26570349543908350446707969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17713566362605566964471979 26570349543908350446707969)
              ·
                refine ⟨19927762157931262835030977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26570349543908350446707969 19927762157931262835030977)
                ·
                  refine ⟨14945821618448447126273233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19927762157931262835030977 14945821618448447126273233)
                  ·
                    refine ⟨11209366213836335344704925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14945821618448447126273233 11209366213836335344704925)
                    ·
                      refine ⟨4203512330188625754264347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11209366213836335344704925 4203512330188625754264347)
                      ·
                        rfl

theorem cell23_8186311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_8186311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186311 prefixEnd_8186311 := by exact prefixLift 8186311
  have htrace : WordTrace (prefixWord ++ tailWord_8186311) baseStart_8186311 baseEnd_8186311 := by
    simpa [prefixWord, tailWord_8186311, baseEnd_8186311] using wordTrace_append hprefix tailTrace_8186311
  have hstable : (prefixWord ++ tailWord_8186311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186311).length < 2 ^ (prefixWord ++ tailWord_8186311).sum := by decide
  have hdescent : baseEnd_8186311 < baseStart_8186311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186314 : List Nat := [3, 1, 2, 1, 2, 2, 2, 4, 6]
def baseStart_8186314 : Nat := 118140960795 + 8186314 * 2 ^ 59
def prefixEnd_8186314 : Nat := 4983230072969 + 3 ^ 40 * 8186314 * 2
def baseEnd_8186314 : Nat := 467057096736732138058537

theorem tailTrace_8186314 : CollatzResearch.WordTrace tailWord_8186314 prefixEnd_8186314 467057096736732138058537 := by
  unfold tailWord_8186314
  simp only [CollatzResearch.WordTrace]
  refine ⟨74644850216097490991749499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199052933909593309311331997 74644850216097490991749499)
  ·
    refine ⟨111967275324146236487624249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74644850216097490991749499 111967275324146236487624249)
    ·
      refine ⟨83975456493109677365718187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111967275324146236487624249 83975456493109677365718187)
      ·
        refine ⟨125963184739664516048577281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83975456493109677365718187 125963184739664516048577281)
        ·
          refine ⟨94472388554748387036432961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125963184739664516048577281 94472388554748387036432961)
          ·
            refine ⟨70854291416061290277324721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94472388554748387036432961 70854291416061290277324721)
            ·
              refine ⟨53140718562045967707993541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70854291416061290277324721 53140718562045967707993541)
              ·
                refine ⟨9963884730383618945248789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53140718562045967707993541 9963884730383618945248789)
                ·
                  refine ⟨467057096736732138058537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9963884730383618945248789 467057096736732138058537)
                  ·
                    rfl

theorem cell23_8186314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_8186314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186314 prefixEnd_8186314 := by exact prefixLift 8186314
  have htrace : WordTrace (prefixWord ++ tailWord_8186314) baseStart_8186314 baseEnd_8186314 := by
    simpa [prefixWord, tailWord_8186314, baseEnd_8186314] using wordTrace_append hprefix tailTrace_8186314
  have hstable : (prefixWord ++ tailWord_8186314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186314).length < 2 ^ (prefixWord ++ tailWord_8186314).sum := by decide
  have hdescent : baseEnd_8186314 < baseStart_8186314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186327 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 1, 11]
def baseStart_8186327 : Nat := 118140960795 + 8186327 * 2 ^ 59
def prefixEnd_8186327 : Nat := 4983230072969 + 3 ^ 40 * 8186327 * 2
def baseEnd_8186327 : Nat := 1401173515293032563888091

theorem tailTrace_8186327 : CollatzResearch.WordTrace tailWord_8186327 prefixEnd_8186327 1401173515293032563888091 := by
  unfold tailWord_8186327
  simp only [CollatzResearch.WordTrace]
  refine ⟨298579875013342867187221235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199053250008895244791480823 298579875013342867187221235)
  ·
    refine ⟨447869812520014300780831853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298579875013342867187221235 447869812520014300780831853)
    ·
      refine ⟨167951179695005362792811945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447869812520014300780831853 167951179695005362792811945)
      ·
        refine ⟨125963384771254022094608959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167951179695005362792811945 125963384771254022094608959)
        ·
          refine ⟨188945077156881033141913439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125963384771254022094608959 188945077156881033141913439)
          ·
            refine ⟨283417615735321549712870159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188945077156881033141913439 283417615735321549712870159)
            ·
              refine ⟨425126423602982324569305239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283417615735321549712870159 425126423602982324569305239)
              ·
                refine ⟨637689635404473486853957859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425126423602982324569305239 637689635404473486853957859)
                ·
                  refine ⟨956534453106710230280936789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637689635404473486853957859 956534453106710230280936789)
                  ·
                    refine ⟨1401173515293032563888091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 956534453106710230280936789 1401173515293032563888091)
                    ·
                      rfl

theorem cell23_8186327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_8186327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186327 prefixEnd_8186327 := by exact prefixLift 8186327
  have htrace : WordTrace (prefixWord ++ tailWord_8186327) baseStart_8186327 baseEnd_8186327 := by
    simpa [prefixWord, tailWord_8186327, baseEnd_8186327] using wordTrace_append hprefix tailTrace_8186327
  have hstable : (prefixWord ++ tailWord_8186327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186327).length < 2 ^ (prefixWord ++ tailWord_8186327).sum := by decide
  have hdescent : baseEnd_8186327 < baseStart_8186327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186394 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_8186394 : Nat := 118140960795 + 8186394 * 2 ^ 59
def prefixEnd_8186394 : Nat := 4983230072969 + 3 ^ 40 * 8186394 * 2
def baseEnd_8186394 : Nat := 4203554949082948929526465

theorem tailTrace_8186394 : CollatzResearch.WordTrace tailWord_8186394 prefixEnd_8186394 4203554949082948929526465 := by
  unfold tailWord_8186394
  simp only [CollatzResearch.WordTrace]
  refine ⟨74645579676025034407477559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199054879136066758419940157 74645579676025034407477559)
  ·
    refine ⟨111968369514037551611216339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74645579676025034407477559 111968369514037551611216339)
    ·
      refine ⟨167952554271056327416824509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111968369514037551611216339 167952554271056327416824509)
      ·
        refine ⟨62982207851646122781309191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167952554271056327416824509 62982207851646122781309191)
        ·
          refine ⟨94473311777469184171963787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62982207851646122781309191 94473311777469184171963787)
          ·
            refine ⟨141709967666203776257945681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94473311777469184171963787 141709967666203776257945681)
            ·
              refine ⟨106282475749652832193459261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141709967666203776257945681 106282475749652832193459261)
              ·
                refine ⟨39855928406119812072547223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106282475749652832193459261 39855928406119812072547223)
                ·
                  refine ⟨59783892609179718108820835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39855928406119812072547223 59783892609179718108820835)
                  ·
                    refine ⟨89675838913769577163231253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59783892609179718108820835 89675838913769577163231253)
                    ·
                      refine ⟨4203554949082948929526465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89675838913769577163231253 4203554949082948929526465)
                      ·
                        rfl

theorem cell23_8186394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_8186394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186394 prefixEnd_8186394 := by exact prefixLift 8186394
  have htrace : WordTrace (prefixWord ++ tailWord_8186394) baseStart_8186394 baseEnd_8186394 := by
    simpa [prefixWord, tailWord_8186394, baseEnd_8186394] using wordTrace_append hprefix tailTrace_8186394
  have hstable : (prefixWord ++ tailWord_8186394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186394).length < 2 ^ (prefixWord ++ tailWord_8186394).sum := by decide
  have hdescent : baseEnd_8186394 < baseStart_8186394 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186401 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_8186401 : Nat := 118140960795 + 8186401 * 2 ^ 59
def prefixEnd_8186401 : Nat := 4983230072969 + 3 ^ 40 * 8186401 * 2
def baseEnd_8186401 : Nat := 4203558543447530402138933

theorem tailTrace_8186401 : CollatzResearch.WordTrace tailWord_8186401 prefixEnd_8186401 4203558543447530402138933 := by
  unfold tailWord_8186401
  simp only [CollatzResearch.WordTrace]
  refine ⟨298582574015074777825415057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199055049343383185216943371 298582574015074777825415057)
  ·
    refine ⟨223936930511306083369061293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298582574015074777825415057 223936930511306083369061293)
    ·
      refine ⟨83976348941739781263397985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223936930511306083369061293 83976348941739781263397985)
      ·
        refine ⟨62982261706304835947548489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83976348941739781263397985 62982261706304835947548489)
        ·
          refine ⟨47236696279728626960661367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62982261706304835947548489 47236696279728626960661367)
          ·
            refine ⟨70855044419592940440992051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47236696279728626960661367 70855044419592940440992051)
            ·
              refine ⟨106282566629389410661488077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70855044419592940440992051 106282566629389410661488077)
              ·
                refine ⟨39855962486021028998058029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106282566629389410661488077 39855962486021028998058029)
                ·
                  refine ⟨14945985932257885874271761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39855962486021028998058029 14945985932257885874271761)
                  ·
                    refine ⟨11209489449193414405703821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14945985932257885874271761 11209489449193414405703821)
                    ·
                      refine ⟨4203558543447530402138933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11209489449193414405703821 4203558543447530402138933)
                      ·
                        rfl

theorem cell23_8186401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_8186401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186401 prefixEnd_8186401 := by exact prefixLift 8186401
  have htrace : WordTrace (prefixWord ++ tailWord_8186401) baseStart_8186401 baseEnd_8186401 := by
    simpa [prefixWord, tailWord_8186401, baseEnd_8186401] using wordTrace_append hprefix tailTrace_8186401
  have hstable : (prefixWord ++ tailWord_8186401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186401).length < 2 ^ (prefixWord ++ tailWord_8186401).sum := by decide
  have hdescent : baseEnd_8186401 < baseStart_8186401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186445 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_8186445 : Nat := 118140960795 + 8186445 * 2 ^ 59
def prefixEnd_8186445 : Nat := 4983230072969 + 3 ^ 40 * 8186445 * 2
def baseEnd_8186445 : Nat := 4203581136596328229988731

theorem tailTrace_8186445 : CollatzResearch.WordTrace tailWord_8186445 prefixEnd_8186445 4203581136596328229988731 := by
  unfold tailWord_8186445
  simp only [CollatzResearch.WordTrace]
  refine ⟨298584178826915373340016789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199056119217943582226677859 298584178826915373340016789)
  ·
    refine ⟨13996133382511658125313287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 298584178826915373340016789 13996133382511658125313287)
    ·
      refine ⟨20994200073767487187969931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13996133382511658125313287 20994200073767487187969931)
      ·
        refine ⟨31491300110651230781954897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20994200073767487187969931 31491300110651230781954897)
        ·
          refine ⟨23618475082988423086466173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31491300110651230781954897 23618475082988423086466173)
          ·
            refine ⟨8856928156120658657424815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23618475082988423086466173 8856928156120658657424815)
            ·
              refine ⟨13285392234180987986137223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8856928156120658657424815 13285392234180987986137223)
              ·
                refine ⟨19928088351271481979205835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13285392234180987986137223 19928088351271481979205835)
                ·
                  refine ⟨29892132526907222968808753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19928088351271481979205835 29892132526907222968808753)
                  ·
                    refine ⟨22419099395180417226606565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29892132526907222968808753 22419099395180417226606565)
                    ·
                      refine ⟨4203581136596328229988731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22419099395180417226606565 4203581136596328229988731)
                      ·
                        rfl

theorem cell23_8186445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_8186445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186445 prefixEnd_8186445 := by exact prefixLift 8186445
  have htrace : WordTrace (prefixWord ++ tailWord_8186445) baseStart_8186445 baseEnd_8186445 := by
    simpa [prefixWord, tailWord_8186445, baseEnd_8186445] using wordTrace_append hprefix tailTrace_8186445
  have hstable : (prefixWord ++ tailWord_8186445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186445).length < 2 ^ (prefixWord ++ tailWord_8186445).sum := by decide
  have hdescent : baseEnd_8186445 < baseStart_8186445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186464 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 1, 8]
def baseStart_8186464 : Nat := 118140960795 + 8186464 * 2 ^ 59
def prefixEnd_8186464 : Nat := 4983230072969 + 3 ^ 40 * 8186464 * 2
def baseEnd_8186464 : Nat := 1401196964242921218550381

theorem tailTrace_8186464 : CollatzResearch.WordTrace tailWord_8186464 prefixEnd_8186464 1401196964242921218550381 := by
  unfold tailWord_8186464
  simp only [CollatzResearch.WordTrace]
  refine ⟨149292435906923269792479223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199056581209231026389972297 149292435906923269792479223)
  ·
    refine ⟨223938653860384904688718835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149292435906923269792479223 223938653860384904688718835)
    ·
      refine ⟨335907980790577357033078253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223938653860384904688718835 335907980790577357033078253)
      ·
        refine ⟨125965492796466508887404345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335907980790577357033078253 125965492796466508887404345)
        ·
          refine ⟨94474119597349881665553259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125965492796466508887404345 94474119597349881665553259)
          ·
            refine ⟨141711179396024822498329889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94474119597349881665553259 141711179396024822498329889)
            ·
              refine ⟨106283384547018616873747417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141711179396024822498329889 106283384547018616873747417)
              ·
                refine ⟨79712538410263962655310563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106283384547018616873747417 79712538410263962655310563)
                ·
                  refine ⟨119568807615395943982965845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79712538410263962655310563 119568807615395943982965845)
                  ·
                    refine ⟨1401196964242921218550381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119568807615395943982965845 1401196964242921218550381)
                    ·
                      rfl

theorem cell23_8186464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_8186464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186464 prefixEnd_8186464 := by exact prefixLift 8186464
  have htrace : WordTrace (prefixWord ++ tailWord_8186464) baseStart_8186464 baseEnd_8186464 := by
    simpa [prefixWord, tailWord_8186464, baseEnd_8186464] using wordTrace_append hprefix tailTrace_8186464
  have hstable : (prefixWord ++ tailWord_8186464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186464).length < 2 ^ (prefixWord ++ tailWord_8186464).sum := by decide
  have hdescent : baseEnd_8186464 < baseStart_8186464 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186522 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2]
def baseStart_8186522 : Nat := 118140960795 + 8186522 * 2 ^ 59
def prefixEnd_8186522 : Nat := 4983230072969 + 3 ^ 40 * 8186522 * 2
def baseEnd_8186522 : Nat := 4203620674606724428725877

theorem tailTrace_8186522 : CollatzResearch.WordTrace tailWord_8186522 prefixEnd_8186522 4203620674606724428725877 := by
  unfold tailWord_8186522
  simp only [CollatzResearch.WordTrace]
  refine ⟨74646746811909103872642455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199057991498424276993713213 74646746811909103872642455)
  ·
    refine ⟨111970120217863655808963683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74646746811909103872642455 111970120217863655808963683)
    ·
      refine ⟨167955180326795483713445525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111970120217863655808963683 167955180326795483713445525)
      ·
        refine ⟨7872899077818538299067759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167955180326795483713445525 7872899077818538299067759)
        ·
          refine ⟨11809348616727807448601639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872899077818538299067759 11809348616727807448601639)
          ·
            refine ⟨17714022925091711172902459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11809348616727807448601639 17714022925091711172902459)
            ·
              refine ⟨26571034387637566759353689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17714022925091711172902459 26571034387637566759353689)
              ·
                refine ⟨19928275790728175069515267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26571034387637566759353689 19928275790728175069515267)
                ·
                  refine ⟨29892413686092262604272901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19928275790728175069515267 29892413686092262604272901)
                  ·
                    refine ⟨5604827566142299238301169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29892413686092262604272901 5604827566142299238301169)
                    ·
                      refine ⟨4203620674606724428725877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5604827566142299238301169 4203620674606724428725877)
                      ·
                        rfl

theorem cell23_8186522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_8186522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186522 prefixEnd_8186522 := by exact prefixLift 8186522
  have htrace : WordTrace (prefixWord ++ tailWord_8186522) baseStart_8186522 baseEnd_8186522 := by
    simpa [prefixWord, tailWord_8186522, baseEnd_8186522] using wordTrace_append hprefix tailTrace_8186522
  have hstable : (prefixWord ++ tailWord_8186522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186522).length < 2 ^ (prefixWord ++ tailWord_8186522).sum := by decide
  have hdescent : baseEnd_8186522 < baseStart_8186522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186591 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 6]
def baseStart_8186591 : Nat := 118140960795 + 8186591 * 2 ^ 59
def prefixEnd_8186591 : Nat := 4983230072969 + 3 ^ 40 * 8186591 * 2
def baseEnd_8186591 : Nat := 4203656104771884658763059

theorem tailTrace_8186591 : CollatzResearch.WordTrace tailWord_8186591 prefixEnd_8186591 4203656104771884658763059 := by
  unfold tailWord_8186591
  simp only [CollatzResearch.WordTrace]
  refine ⟨298589503884386440274831627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199059669256257626849887751 298589503884386440274831627)
  ·
    refine ⟨447884255826579660412247441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298589503884386440274831627 447884255826579660412247441)
    ·
      refine ⟨335913191869934745309185581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447884255826579660412247441 335913191869934745309185581)
      ·
        refine ⟨125967446951225529490944593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335913191869934745309185581 125967446951225529490944593)
        ·
          refine ⟨94475585213419147118208445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125967446951225529490944593 94475585213419147118208445)
          ·
            refine ⟨35428344455032180169328167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94475585213419147118208445 35428344455032180169328167)
            ·
              refine ⟨53142516682548270253992251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35428344455032180169328167 53142516682548270253992251)
              ·
                refine ⟨79713775023822405380988377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53142516682548270253992251 79713775023822405380988377)
                ·
                  refine ⟨59785331267866804035741283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79713775023822405380988377 59785331267866804035741283)
                  ·
                    refine ⟨89677996901800206053611925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59785331267866804035741283 89677996901800206053611925)
                    ·
                      refine ⟨4203656104771884658763059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89677996901800206053611925 4203656104771884658763059)
                      ·
                        rfl

theorem cell23_8186591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_8186591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186591 prefixEnd_8186591 := by exact prefixLift 8186591
  have htrace : WordTrace (prefixWord ++ tailWord_8186591) baseStart_8186591 baseEnd_8186591 := by
    simpa [prefixWord, tailWord_8186591, baseEnd_8186591] using wordTrace_append hprefix tailTrace_8186591
  have hstable : (prefixWord ++ tailWord_8186591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186591).length < 2 ^ (prefixWord ++ tailWord_8186591).sum := by decide
  have hdescent : baseEnd_8186591 < baseStart_8186591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186595 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 2, 4, 2]
def baseStart_8186595 : Nat := 118140960795 + 8186595 * 2 ^ 59
def prefixEnd_8186595 : Nat := 4983230072969 + 3 ^ 40 * 8186595 * 2
def baseEnd_8186595 : Nat := 4203658158694502643113041

theorem tailTrace_8186595 : CollatzResearch.WordTrace tailWord_8186595 prefixEnd_8186595 4203658158694502643113041 := by
  unfold tailWord_8186595
  simp only [CollatzResearch.WordTrace]
  refine ⟨298589649776371948957977239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199059766517581299305318159 298589649776371948957977239)
  ·
    refine ⟨447884474664557923436965859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298589649776371948957977239 447884474664557923436965859)
    ·
      refine ⟨671826711996836885155448789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447884474664557923436965859 671826711996836885155448789)
      ·
        refine ⟨15745938562425864495830831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 671826711996836885155448789 15745938562425864495830831)
        ·
          refine ⟨23618907843638796743746247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15745938562425864495830831 23618907843638796743746247)
          ·
            refine ⟨35428361765458195115619371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23618907843638796743746247 35428361765458195115619371)
            ·
              refine ⟨53142542648187292673429057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35428361765458195115619371 53142542648187292673429057)
              ·
                refine ⟨39856906986140469505071793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53142542648187292673429057 39856906986140469505071793)
                ·
                  refine ⟨29892680239605352128803845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39856906986140469505071793 29892680239605352128803845)
                  ·
                    refine ⟨5604877544926003524150721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29892680239605352128803845 5604877544926003524150721)
                    ·
                      refine ⟨4203658158694502643113041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5604877544926003524150721 4203658158694502643113041)
                      ·
                        rfl

theorem cell23_8186595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_8186595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186595 prefixEnd_8186595 := by exact prefixLift 8186595
  have htrace : WordTrace (prefixWord ++ tailWord_8186595) baseStart_8186595 baseEnd_8186595 := by
    simpa [prefixWord, tailWord_8186595, baseEnd_8186595] using wordTrace_append hprefix tailTrace_8186595
  have hstable : (prefixWord ++ tailWord_8186595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186595).length < 2 ^ (prefixWord ++ tailWord_8186595).sum := by decide
  have hdescent : baseEnd_8186595 < baseStart_8186595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186605 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_8186605 : Nat := 118140960795 + 8186605 * 2 ^ 59
def prefixEnd_8186605 : Nat := 4983230072969 + 3 ^ 40 * 8186605 * 2
def baseEnd_8186605 : Nat := 1401221097833682534662665

theorem tailTrace_8186605 : CollatzResearch.WordTrace tailWord_8186605 prefixEnd_8186605 1401221097833682534662665 := by
  unfold tailWord_8186605
  simp only [CollatzResearch.WordTrace]
  refine ⟨298590014506335720665841269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199060009670890480443894179 298590014506335720665841269)
  ·
    refine ⟨27992813859968973812422619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298590014506335720665841269 27992813859968973812422619)
    ·
      refine ⟨41989220789953460718633929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27992813859968973812422619 41989220789953460718633929)
      ·
        refine ⟨31491915592465095538975447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41989220789953460718633929 31491915592465095538975447)
        ·
          refine ⟨47237873388697643308463171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31491915592465095538975447 47237873388697643308463171)
          ·
            refine ⟨70856810083046464962694757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47237873388697643308463171 70856810083046464962694757)
            ·
              refine ⟨13285651890571212180505267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70856810083046464962694757 13285651890571212180505267)
              ·
                refine ⟨19928477835856818270757901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13285651890571212180505267 19928477835856818270757901)
                ·
                  refine ⟨7473179188446306851534213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19928477835856818270757901 7473179188446306851534213)
                  ·
                    refine ⟨1401221097833682534662665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7473179188446306851534213 1401221097833682534662665)
                    ·
                      rfl

theorem cell23_8186605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_8186605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186605 prefixEnd_8186605 := by exact prefixLift 8186605
  have htrace : WordTrace (prefixWord ++ tailWord_8186605) baseStart_8186605 baseEnd_8186605 := by
    simpa [prefixWord, tailWord_8186605, baseEnd_8186605] using wordTrace_append hprefix tailTrace_8186605
  have hstable : (prefixWord ++ tailWord_8186605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186605).length < 2 ^ (prefixWord ++ tailWord_8186605).sum := by decide
  have hdescent : baseEnd_8186605 < baseStart_8186605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186621 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_8186621 : Nat := 118140960795 + 8186621 * 2 ^ 59
def prefixEnd_8186621 : Nat := 4983230072969 + 3 ^ 40 * 8186621 * 2
def baseEnd_8186621 : Nat := 4203671509191519541387921

theorem tailTrace_8186621 : CollatzResearch.WordTrace tailWord_8186621 prefixEnd_8186621 4203671509191519541387921 := by
  unfold tailWord_8186621
  simp only [CollatzResearch.WordTrace]
  refine ⟨298590598074277755398423717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199060398716185170265615811 298590598074277755398423717)
  ·
    refine ⟨55985737138927079137204447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298590598074277755398423717 55985737138927079137204447)
    ·
      refine ⟨83978605708390618705806671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55985737138927079137204447 83978605708390618705806671)
      ·
        refine ⟨125967908562585928058710007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83978605708390618705806671 125967908562585928058710007)
        ·
          refine ⟨188951862843878892088065011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125967908562585928058710007 188951862843878892088065011)
          ·
            refine ⟨283427794265818338132097517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188951862843878892088065011 283427794265818338132097517)
            ·
              refine ⟨106285422849681876799536569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283427794265818338132097517 106285422849681876799536569)
              ·
                refine ⟨79714067137261407599652427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106285422849681876799536569 79714067137261407599652427)
                ·
                  refine ⟨119571100705892111399478641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79714067137261407599652427 119571100705892111399478641)
                  ·
                    refine ⟨89678325529419083549608981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119571100705892111399478641 89678325529419083549608981)
                    ·
                      refine ⟨4203671509191519541387921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89678325529419083549608981 4203671509191519541387921)
                      ·
                        rfl

theorem cell23_8186621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_8186621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186621 prefixEnd_8186621 := by exact prefixLift 8186621
  have htrace : WordTrace (prefixWord ++ tailWord_8186621) baseStart_8186621 baseEnd_8186621 := by
    simpa [prefixWord, tailWord_8186621, baseEnd_8186621] using wordTrace_append hprefix tailTrace_8186621
  have hstable : (prefixWord ++ tailWord_8186621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186621).length < 2 ^ (prefixWord ++ tailWord_8186621).sum := by decide
  have hdescent : baseEnd_8186621 < baseStart_8186621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186628 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_8186628 : Nat := 118140960795 + 8186628 * 2 ^ 59
def prefixEnd_8186628 : Nat := 4983230072969 + 3 ^ 40 * 8186628 * 2
def baseEnd_8186628 : Nat := 4203675103556101014000389

theorem tailTrace_8186628 : CollatzResearch.WordTrace tailWord_8186628 prefixEnd_8186628 4203675103556101014000389 := by
  unfold tailWord_8186628
  simp only [CollatzResearch.WordTrace]
  refine ⟨149295426692626197796964269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199060568923501597062619025 149295426692626197796964269)
  ·
    refine ⟨55985785009734824173861601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149295426692626197796964269 55985785009734824173861601)
    ·
      refine ⟨41989338757301118130396201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55985785009734824173861601 41989338757301118130396201)
      ·
        refine ⟨31492004067975838597797151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41989338757301118130396201 31492004067975838597797151)
        ·
          refine ⟨47238006101963757896695727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31492004067975838597797151 47238006101963757896695727)
          ·
            refine ⟨70857009152945636845043591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47238006101963757896695727 70857009152945636845043591)
            ·
              refine ⟨106285513729418455267565387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70857009152945636845043591 106285513729418455267565387)
              ·
                refine ⟨159428270594127682901348081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106285513729418455267565387 159428270594127682901348081)
                ·
                  refine ⟨119571202945595762176011061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159428270594127682901348081 119571202945595762176011061)
                  ·
                    refine ⟨11209800276149602704001037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119571202945595762176011061 11209800276149602704001037)
                    ·
                      refine ⟨4203675103556101014000389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11209800276149602704001037 4203675103556101014000389)
                      ·
                        rfl

theorem cell23_8186628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_8186628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186628 prefixEnd_8186628 := by exact prefixLift 8186628
  have htrace : WordTrace (prefixWord ++ tailWord_8186628) baseStart_8186628 baseEnd_8186628 := by
    simpa [prefixWord, tailWord_8186628, baseEnd_8186628] using wordTrace_append hprefix tailTrace_8186628
  have hstable : (prefixWord ++ tailWord_8186628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186628).length < 2 ^ (prefixWord ++ tailWord_8186628).sum := by decide
  have hdescent : baseEnd_8186628 < baseStart_8186628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186655 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 4, 3, 2]
def baseStart_8186655 : Nat := 118140960795 + 8186655 * 2 ^ 59
def prefixEnd_8186655 : Nat := 4983230072969 + 3 ^ 40 * 8186655 * 2
def baseEnd_8186655 : Nat := 4203688967533772408362765

theorem tailTrace_8186655 : CollatzResearch.WordTrace tailWord_8186655 prefixEnd_8186655 4203688967533772408362765 := by
  unfold tailWord_8186655
  simp only [CollatzResearch.WordTrace]
  refine ⟨298591838156154579205161419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199061225437436386136774279 298591838156154579205161419)
  ·
    refine ⟨447887757234231868807742129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298591838156154579205161419 447887757234231868807742129)
    ·
      refine ⟨335915817925673901605806597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447887757234231868807742129 335915817925673901605806597)
      ·
        refine ⟨62984215861063856551088737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335915817925673901605806597 62984215861063856551088737)
        ·
          refine ⟨47238161895797892413316553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62984215861063856551088737 47238161895797892413316553)
          ·
            refine ⟨35428621421848419309987415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47238161895797892413316553 35428621421848419309987415)
            ·
              refine ⟨53142932132772628964981123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35428621421848419309987415 53142932132772628964981123)
              ·
                refine ⟨79714398199158943447471685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53142932132772628964981123 79714398199158943447471685)
                ·
                  refine ⟨14946449662342301896400941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79714398199158943447471685 14946449662342301896400941)
                  ·
                    refine ⟨5604918623378363211150353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14946449662342301896400941 5604918623378363211150353)
                    ·
                      refine ⟨4203688967533772408362765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5604918623378363211150353 4203688967533772408362765)
                      ·
                        rfl

theorem cell23_8186655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_8186655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186655 prefixEnd_8186655 := by exact prefixLift 8186655
  have htrace : WordTrace (prefixWord ++ tailWord_8186655) baseStart_8186655 baseEnd_8186655 := by
    simpa [prefixWord, tailWord_8186655, baseEnd_8186655] using wordTrace_append hprefix tailTrace_8186655
  have hstable : (prefixWord ++ tailWord_8186655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186655).length < 2 ^ (prefixWord ++ tailWord_8186655).sum := by decide
  have hdescent : baseEnd_8186655 < baseStart_8186655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186668 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 4]
def baseStart_8186668 : Nat := 118140960795 + 8186668 * 2 ^ 59
def prefixEnd_8186668 : Nat := 4983230072969 + 3 ^ 40 * 8186668 * 2
def baseEnd_8186668 : Nat := 4203695642782280857500205

theorem tailTrace_8186668 : CollatzResearch.WordTrace tailWord_8186668 prefixEnd_8186668 4203695642782280857500205 := by
  unfold tailWord_8186668
  simp only [CollatzResearch.WordTrace]
  refine ⟨149296156152553741212692329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199061541536738321616923105 149296156152553741212692329)
  ·
    refine ⟨111972117114415305909519247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149296156152553741212692329 111972117114415305909519247)
    ·
      refine ⟨167958175671622958864278871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111972117114415305909519247 167958175671622958864278871)
      ·
        refine ⟨251937263507434438296418307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167958175671622958864278871 251937263507434438296418307)
        ·
          refine ⟨377905895261151657444627461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251937263507434438296418307 377905895261151657444627461)
          ·
            refine ⟨70857355361465935770867649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377905895261151657444627461 70857355361465935770867649)
            ·
              refine ⟨53143016521099451828150737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70857355361465935770867649 53143016521099451828150737)
              ·
                refine ⟨39857262390824588871113053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53143016521099451828150737 39857262390824588871113053)
                ·
                  refine ⟨14946473396559220826667395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39857262390824588871113053 14946473396559220826667395)
                  ·
                    refine ⟨22419710094838831240001093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14946473396559220826667395 22419710094838831240001093)
                    ·
                      refine ⟨4203695642782280857500205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22419710094838831240001093 4203695642782280857500205)
                      ·
                        rfl

theorem cell23_8186668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_8186668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186668 prefixEnd_8186668 := by exact prefixLift 8186668
  have htrace : WordTrace (prefixWord ++ tailWord_8186668) baseStart_8186668 baseEnd_8186668 := by
    simpa [prefixWord, tailWord_8186668, baseEnd_8186668] using wordTrace_append hprefix tailTrace_8186668
  have hstable : (prefixWord ++ tailWord_8186668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186668).length < 2 ^ (prefixWord ++ tailWord_8186668).sum := by decide
  have hdescent : baseEnd_8186668 < baseStart_8186668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186682 : List Nat := [3, 1, 1, 1, 6, 2, 1, 2, 1, 5]
def baseStart_8186682 : Nat := 118140960795 + 8186682 * 2 ^ 59
def prefixEnd_8186682 : Nat := 4983230072969 + 3 ^ 40 * 8186682 * 2
def baseEnd_8186682 : Nat := 1401234277170481267575047

theorem tailTrace_8186682 : CollatzResearch.WordTrace tailWord_8186682 prefixEnd_8186682 1401234277170481267575047 := by
  unfold tailWord_8186682
  simp only [CollatzResearch.WordTrace]
  refine ⟨74648205731764190704098575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199061881951371175210929533 74648205731764190704098575)
  ·
    refine ⟨111972308597646286056147863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74648205731764190704098575 111972308597646286056147863)
    ·
      refine ⟨167958462896469429084221795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111972308597646286056147863 167958462896469429084221795)
      ·
        refine ⟨251937694344704143626332693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167958462896469429084221795 251937694344704143626332693)
        ·
          refine ⟨11809579422408006732484345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251937694344704143626332693 11809579422408006732484345)
          ·
            refine ⟨8857184566806005049363259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11809579422408006732484345 8857184566806005049363259)
            ·
              refine ⟨13285776850209007574044889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8857184566806005049363259 13285776850209007574044889)
              ·
                refine ⟨9964332637656755680533667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13285776850209007574044889 9964332637656755680533667)
                ·
                  refine ⟨14946498956485133520800501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9964332637656755680533667 14946498956485133520800501)
                  ·
                    refine ⟨1401234277170481267575047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14946498956485133520800501 1401234277170481267575047)
                    ·
                      rfl

theorem cell23_8186682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_8186682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186682 prefixEnd_8186682 := by exact prefixLift 8186682
  have htrace : WordTrace (prefixWord ++ tailWord_8186682) baseStart_8186682 baseEnd_8186682 := by
    simpa [prefixWord, tailWord_8186682, baseEnd_8186682] using wordTrace_append hprefix tailTrace_8186682
  have hstable : (prefixWord ++ tailWord_8186682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186682).length < 2 ^ (prefixWord ++ tailWord_8186682).sum := by decide
  have hdescent : baseEnd_8186682 < baseStart_8186682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186691 : List Nat := [1, 1, 1, 3, 1, 4, 1, 11]
def baseStart_8186691 : Nat := 118140960795 + 8186691 * 2 ^ 59
def prefixEnd_8186691 : Nat := 4983230072969 + 3 ^ 40 * 8186691 * 2
def baseEnd_8186691 : Nat := 155692868623604972870837

theorem tailTrace_8186691 : CollatzResearch.WordTrace tailWord_8186691 prefixEnd_8186691 155692868623604972870837 := by
  unfold tailWord_8186691
  simp only [CollatzResearch.WordTrace]
  refine ⟨298593151184024157353471927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199062100789349438235647951 298593151184024157353471927)
  ·
    refine ⟨447889726776036236030207891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298593151184024157353471927 447889726776036236030207891)
    ·
      refine ⟨671834590164054354045311837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447889726776036236030207891 671834590164054354045311837)
      ·
        refine ⟨251937971311520382766991939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 671834590164054354045311837 251937971311520382766991939)
        ·
          refine ⟨377906956967280574150487909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251937971311520382766991939 377906956967280574150487909)
          ·
            refine ⟨70857554431365107653216483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377906956967280574150487909 70857554431365107653216483)
            ·
              refine ⟨106286331647047661479824725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70857554431365107653216483 106286331647047661479824725)
              ·
                refine ⟨155692868623604972870837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 106286331647047661479824725 155692868623604972870837)
                ·
                  rfl

theorem cell23_8186691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 11].length) (baseStart_8186691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186691 prefixEnd_8186691 := by exact prefixLift 8186691
  have htrace : WordTrace (prefixWord ++ tailWord_8186691) baseStart_8186691 baseEnd_8186691 := by
    simpa [prefixWord, tailWord_8186691, baseEnd_8186691] using wordTrace_append hprefix tailTrace_8186691
  have hstable : (prefixWord ++ tailWord_8186691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186691).length < 2 ^ (prefixWord ++ tailWord_8186691).sum := by decide
  have hdescent : baseEnd_8186691 < baseStart_8186691 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186708 : List Nat := [2, 4, 1, 1, 4, 11]
def baseStart_8186708 : Nat := 118140960795 + 8186708 * 2 ^ 59
def prefixEnd_8186708 : Nat := 4983230072969 + 3 ^ 40 * 8186708 * 2
def baseEnd_8186708 : Nat := 17299243547359920580247

theorem tailTrace_8186708 : CollatzResearch.WordTrace tailWord_8186708 prefixEnd_8186708 17299243547359920580247 := by
  unfold tailWord_8186708
  simp only [CollatzResearch.WordTrace]
  refine ⟨149296885612481284628420389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199062514149975046171227185 149296885612481284628420389)
  ·
    refine ⟨27993166052340240867828823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149296885612481284628420389 27993166052340240867828823)
    ·
      refine ⟨41989749078510361301743235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27993166052340240867828823 41989749078510361301743235)
      ·
        refine ⟨62984623617765541952614853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41989749078510361301743235 62984623617765541952614853)
        ·
          refine ⟨11809616928331039116115285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62984623617765541952614853 11809616928331039116115285)
          ·
            refine ⟨17299243547359920580247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11809616928331039116115285 17299243547359920580247)
            ·
              rfl

theorem cell23_8186708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 11].length) (baseStart_8186708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186708 prefixEnd_8186708 := by exact prefixLift 8186708
  have htrace : WordTrace (prefixWord ++ tailWord_8186708) baseStart_8186708 baseEnd_8186708 := by
    simpa [prefixWord, tailWord_8186708, baseEnd_8186708] using wordTrace_append hprefix tailTrace_8186708
  have hstable : (prefixWord ++ tailWord_8186708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186708).length < 2 ^ (prefixWord ++ tailWord_8186708).sum := by decide
  have hdescent : baseEnd_8186708 < baseStart_8186708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186719 : List Nat := [1, 1, 2, 3, 1, 3, 3, 4, 1, 2, 2]
def baseStart_8186719 : Nat := 118140960795 + 8186719 * 2 ^ 59
def prefixEnd_8186719 : Nat := 4983230072969 + 3 ^ 40 * 8186719 * 2
def baseEnd_8186719 : Nat := 4203721830295660157962471

theorem tailTrace_8186719 : CollatzResearch.WordTrace tailWord_8186719 prefixEnd_8186719 4203721830295660157962471 := by
  unfold tailWord_8186719
  simp only [CollatzResearch.WordTrace]
  refine ⟨298594172427922718135491211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199062781618615145423660807 298594172427922718135491211)
  ·
    refine ⟨447891258641884077203236817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298594172427922718135491211 447891258641884077203236817)
    ·
      refine ⟨335918443981413057902427613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447891258641884077203236817 335918443981413057902427613)
      ·
        refine ⟨125969416493029896713410355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335918443981413057902427613 125969416493029896713410355)
        ·
          refine ⟨188954124739544845070115533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125969416493029896713410355 188954124739544845070115533)
          ·
            refine ⟨70857796777329316901293325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188954124739544845070115533 70857796777329316901293325)
            ·
              refine ⟨26571673791498493837984997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70857796777329316901293325 26571673791498493837984997)
              ·
                refine ⟨4982188835905967594622187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26571673791498493837984997 4982188835905967594622187)
                ·
                  refine ⟨7473283253858951391933281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982188835905967594622187 7473283253858951391933281)
                  ·
                    refine ⟨5604962440394213543949961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7473283253858951391933281 5604962440394213543949961)
                    ·
                      refine ⟨4203721830295660157962471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5604962440394213543949961 4203721830295660157962471)
                      ·
                        rfl

theorem cell23_8186719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_8186719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186719 prefixEnd_8186719 := by exact prefixLift 8186719
  have htrace : WordTrace (prefixWord ++ tailWord_8186719) baseStart_8186719 baseEnd_8186719 := by
    simpa [prefixWord, tailWord_8186719, baseEnd_8186719] using wordTrace_append hprefix tailTrace_8186719
  have hstable : (prefixWord ++ tailWord_8186719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186719).length < 2 ^ (prefixWord ++ tailWord_8186719).sum := by decide
  have hdescent : baseEnd_8186719 < baseStart_8186719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186742 : List Nat := [5, 1, 1, 3, 1, 2, 3, 7]
def baseStart_8186742 : Nat := 118140960795 + 8186742 * 2 ^ 59
def prefixEnd_8186742 : Nat := 4983230072969 + 3 ^ 40 * 8186742 * 2
def baseEnd_8186742 : Nat := 155693838531507909924995

theorem tailTrace_8186742 : CollatzResearch.WordTrace tailWord_8186742 prefixEnd_8186742 155693838531507909924995 := by
  unfold tailWord_8186742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18662188206677462066473655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199063340871226262042385653 18662188206677462066473655)
  ·
    refine ⟨27993282310016193099710483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18662188206677462066473655 27993282310016193099710483)
    ·
      refine ⟨41989923465024289649565725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27993282310016193099710483 41989923465024289649565725)
      ·
        refine ⟨15746221299384108618587147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41989923465024289649565725 15746221299384108618587147)
        ·
          refine ⟨23619331949076162927880721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15746221299384108618587147 23619331949076162927880721)
          ·
            refine ⟨17714498961807122195910541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23619331949076162927880721 17714498961807122195910541)
            ·
              refine ⟨6642937110677670823466453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17714498961807122195910541 6642937110677670823466453)
              ·
                refine ⟨155693838531507909924995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6642937110677670823466453 155693838531507909924995)
                ·
                  rfl

theorem cell23_8186742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_8186742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186742 prefixEnd_8186742 := by exact prefixLift 8186742
  have htrace : WordTrace (prefixWord ++ tailWord_8186742) baseStart_8186742 baseEnd_8186742 := by
    simpa [prefixWord, tailWord_8186742, baseEnd_8186742] using wordTrace_append hprefix tailTrace_8186742
  have hstable : (prefixWord ++ tailWord_8186742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186742).length < 2 ^ (prefixWord ++ tailWord_8186742).sum := by decide
  have hdescent : baseEnd_8186742 < baseStart_8186742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186785 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 2, 6]
def baseStart_8186785 : Nat := 118140960795 + 8186785 * 2 ^ 59
def prefixEnd_8186785 : Nat := 4983230072969 + 3 ^ 40 * 8186785 * 2
def baseEnd_8186785 : Nat := 1401251906672952299912389

theorem tailTrace_8186785 : CollatzResearch.WordTrace tailWord_8186785 prefixEnd_8186785 1401251906672952299912389 := by
  unfold tailWord_8186785
  simp only [CollatzResearch.WordTrace]
  refine ⟨298596579645683611407393809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199064386430455740938262539 298596579645683611407393809)
  ·
    refine ⟨223947434734262708555545357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298596579645683611407393809 223947434734262708555545357)
    ·
      refine ⟨83980288025348515708329509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223947434734262708555545357 83980288025348515708329509)
      ·
        refine ⟨15746304004752846695311783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83980288025348515708329509 15746304004752846695311783)
        ·
          refine ⟨23619456007129270042967675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15746304004752846695311783 23619456007129270042967675)
          ·
            refine ⟨35429184010693905064451513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23619456007129270042967675 35429184010693905064451513)
            ·
              refine ⟨26571888008020428798338635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35429184010693905064451513 26571888008020428798338635)
              ·
                refine ⟨39857832012030643197507953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26571888008020428798338635 39857832012030643197507953)
                ·
                  refine ⟨29893374009022982398130965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39857832012030643197507953 29893374009022982398130965)
                  ·
                    refine ⟨1401251906672952299912389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29893374009022982398130965 1401251906672952299912389)
                    ·
                      rfl

theorem cell23_8186785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_8186785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186785 prefixEnd_8186785 := by exact prefixLift 8186785
  have htrace : WordTrace (prefixWord ++ tailWord_8186785) baseStart_8186785 baseEnd_8186785 := by
    simpa [prefixWord, tailWord_8186785, baseEnd_8186785] using wordTrace_append hprefix tailTrace_8186785
  have hstable : (prefixWord ++ tailWord_8186785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186785).length < 2 ^ (prefixWord ++ tailWord_8186785).sum := by decide
  have hdescent : baseEnd_8186785 < baseStart_8186785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186786 : List Nat := [3, 3, 1, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_8186786 : Nat := 118140960795 + 8186786 * 2 ^ 59
def prefixEnd_8186786 : Nat := 4983230072969 + 3 ^ 40 * 8186786 * 2
def baseEnd_8186786 : Nat := 4203756233499511395824663

theorem tailTrace_8186786 : CollatzResearch.WordTrace tailWord_8186786 prefixEnd_8186786 4203756233499511395824663 := by
  unfold tailWord_8186786
  simp only [CollatzResearch.WordTrace]
  refine ⟨74649154029669997144545053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199064410745786659052120141 74649154029669997144545053)
  ·
    refine ⟨27993432761126248929204395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74649154029669997144545053 27993432761126248929204395)
    ·
      refine ⟨41990149141689373393806593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27993432761126248929204395 41990149141689373393806593)
      ·
        refine ⟨31492611856267030045354945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41990149141689373393806593 31492611856267030045354945)
        ·
          refine ⟨23619458892200272534016209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31492611856267030045354945 23619458892200272534016209)
          ·
            refine ⟨17714594169150204400512157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23619458892200272534016209 17714594169150204400512157)
            ·
              refine ⟨6642972813431326650192059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17714594169150204400512157 6642972813431326650192059)
              ·
                refine ⟨9964459220146989975288089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6642972813431326650192059 9964459220146989975288089)
                ·
                  refine ⟨7473344415110242481466067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9964459220146989975288089 7473344415110242481466067)
                  ·
                    refine ⟨11210016622665363722199101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7473344415110242481466067 11210016622665363722199101)
                    ·
                      refine ⟨4203756233499511395824663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11210016622665363722199101 4203756233499511395824663)
                      ·
                        rfl

theorem cell23_8186786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_8186786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186786 prefixEnd_8186786 := by exact prefixLift 8186786
  have htrace : WordTrace (prefixWord ++ tailWord_8186786) baseStart_8186786 baseEnd_8186786 := by
    simpa [prefixWord, tailWord_8186786, baseEnd_8186786] using wordTrace_append hprefix tailTrace_8186786
  have hstable : (prefixWord ++ tailWord_8186786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186786).length < 2 ^ (prefixWord ++ tailWord_8186786).sum := by decide
  have hdescent : baseEnd_8186786 < baseStart_8186786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186815 : List Nat := [1, 1, 2, 2, 2, 1, 2, 7, 5]
def baseStart_8186815 : Nat := 118140960795 + 8186815 * 2 ^ 59
def prefixEnd_8186815 : Nat := 4983230072969 + 3 ^ 40 * 8186815 * 2
def baseEnd_8186815 : Nat := 467085680493165753595781

theorem tailTrace_8186815 : CollatzResearch.WordTrace tailWord_8186815 prefixEnd_8186815 467085680493165753595781 := by
  unfold tailWord_8186815
  simp only [CollatzResearch.WordTrace]
  refine ⟨298597673835574926530985899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199065115890383284353990599 298597673835574926530985899)
  ·
    refine ⟨447896510753362389796478849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298597673835574926530985899 447896510753362389796478849)
    ·
      refine ⟨335922383065021792347359137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447896510753362389796478849 335922383065021792347359137)
      ·
        refine ⟨251941787298766344260519353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335922383065021792347359137 251941787298766344260519353)
        ·
          refine ⟨188956340474074758195389515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251941787298766344260519353 188956340474074758195389515)
          ·
            refine ⟨283434510711112137293084273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188956340474074758195389515 283434510711112137293084273)
            ·
              refine ⟨212575883033334102969813205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283434510711112137293084273 212575883033334102969813205)
              ·
                refine ⟨4982247258593768038354997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 212575883033334102969813205 4982247258593768038354997)
                ·
                  refine ⟨467085680493165753595781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4982247258593768038354997 467085680493165753595781)
                  ·
                    rfl

theorem cell23_8186815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 5].length) (baseStart_8186815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186815 prefixEnd_8186815 := by exact prefixLift 8186815
  have htrace : WordTrace (prefixWord ++ tailWord_8186815) baseStart_8186815 baseEnd_8186815 := by
    simpa [prefixWord, tailWord_8186815, baseEnd_8186815] using wordTrace_append hprefix tailTrace_8186815
  have hstable : (prefixWord ++ tailWord_8186815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186815).length < 2 ^ (prefixWord ++ tailWord_8186815).sum := by decide
  have hdescent : baseEnd_8186815 < baseStart_8186815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186905 : List Nat := [1, 2, 1, 2, 1, 1, 6, 3, 6]
def baseStart_8186905 : Nat := 118140960795 + 8186905 * 2 ^ 59
def prefixEnd_8186905 : Nat := 4983230072969 + 3 ^ 40 * 8186905 * 2
def baseEnd_8186905 : Nat := 467090815299710714470735

theorem tailTrace_8186905 : CollatzResearch.WordTrace tailWord_8186905 prefixEnd_8186905 467090815299710714470735 := by
  unfold tailWord_8186905
  simp only [CollatzResearch.WordTrace]
  refine ⟨298600956405248871901762169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199067304270165914601174779 298600956405248871901762169)
  ·
    refine ⟨223950717303936653926321627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298600956405248871901762169 223950717303936653926321627)
    ·
      refine ⟨335926075955904980889482441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223950717303936653926321627 335926075955904980889482441)
      ·
        refine ⟨251944556966928735667111831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335926075955904980889482441 251944556966928735667111831)
        ·
          refine ⟨377916835450393103500667747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251944556966928735667111831 377916835450393103500667747)
          ·
            refine ⟨566875253175589655251001621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377916835450393103500667747 566875253175589655251001621)
            ·
              refine ⟨26572277492605765089890701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 566875253175589655251001621 26572277492605765089890701)
              ·
                refine ⟨9964604059727161908709013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26572277492605765089890701 9964604059727161908709013)
                ·
                  refine ⟨467090815299710714470735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9964604059727161908709013 467090815299710714470735)
                  ·
                    rfl

theorem cell23_8186905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 6].length) (baseStart_8186905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186905 prefixEnd_8186905 := by exact prefixLift 8186905
  have htrace : WordTrace (prefixWord ++ tailWord_8186905) baseStart_8186905 baseEnd_8186905 := by
    simpa [prefixWord, tailWord_8186905, baseEnd_8186905] using wordTrace_append hprefix tailTrace_8186905
  have hstable : (prefixWord ++ tailWord_8186905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186905).length < 2 ^ (prefixWord ++ tailWord_8186905).sum := by decide
  have hdescent : baseEnd_8186905 < baseStart_8186905 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186909 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_8186909 : Nat := 118140960795 + 8186909 * 2 ^ 59
def prefixEnd_8186909 : Nat := 4983230072969 + 3 ^ 40 * 8186909 * 2
def baseEnd_8186909 : Nat := 1401273130540004804862199

theorem tailTrace_8186909 : CollatzResearch.WordTrace tailWord_8186909 prefixEnd_8186909 1401273130540004804862199 := by
  unfold tailWord_8186909
  simp only [CollatzResearch.WordTrace]
  refine ⟨298601102297234380584907781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199067401531489587056605187 298601102297234380584907781)
  ·
    refine ⟨55987706680731446359670209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298601102297234380584907781 55987706680731446359670209)
    ·
      refine ⟨41990780010548584769752657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55987706680731446359670209 41990780010548584769752657)
      ·
        refine ⟨31493085007911438577314493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41990780010548584769752657 31493085007911438577314493)
        ·
          refine ⟨11809906877966789466492935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31493085007911438577314493 11809906877966789466492935)
          ·
            refine ⟨17714860316950184199739403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11809906877966789466492935 17714860316950184199739403)
            ·
              refine ⟨26572290475425276299609105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17714860316950184199739403 26572290475425276299609105)
              ·
                refine ⟨19929217856568957224706829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26572290475425276299609105 19929217856568957224706829)
                ·
                  refine ⟨7473456696213358959265061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19929217856568957224706829 7473456696213358959265061)
                  ·
                    refine ⟨1401273130540004804862199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7473456696213358959265061 1401273130540004804862199)
                    ·
                      rfl

theorem cell23_8186909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_8186909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186909 prefixEnd_8186909 := by exact prefixLift 8186909
  have htrace : WordTrace (prefixWord ++ tailWord_8186909) baseStart_8186909 baseEnd_8186909 := by
    simpa [prefixWord, tailWord_8186909, baseEnd_8186909] using wordTrace_append hprefix tailTrace_8186909
  have hstable : (prefixWord ++ tailWord_8186909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186909).length < 2 ^ (prefixWord ++ tailWord_8186909).sum := by decide
  have hdescent : baseEnd_8186909 < baseStart_8186909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186919 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_8186919 : Nat := 118140960795 + 8186919 * 2 ^ 59
def prefixEnd_8186919 : Nat := 4983230072969 + 3 ^ 40 * 8186919 * 2
def baseEnd_8186919 : Nat := 4203824526426559375461551

theorem tailTrace_8186919 : CollatzResearch.WordTrace tailWord_8186919 prefixEnd_8186919 4203824526426559375461551 := by
  unfold tailWord_8186919
  simp only [CollatzResearch.WordTrace]
  refine ⟨298601467027198152292771811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199067644684798768195181207 298601467027198152292771811)
  ·
    refine ⟨447902200540797228439157717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298601467027198152292771811 447902200540797228439157717)
    ·
      refine ⟨10497707825174935041542759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 447902200540797228439157717 10497707825174935041542759)
      ·
        refine ⟨15746561737762402562314139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10497707825174935041542759 15746561737762402562314139)
        ·
          refine ⟨23619842606643603843471209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15746561737762402562314139 23619842606643603843471209)
          ·
            refine ⟨17714881954982702882603407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23619842606643603843471209 17714881954982702882603407)
            ·
              refine ⟨26572322932474054323905111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17714881954982702882603407 26572322932474054323905111)
              ·
                refine ⟨39858484398711081485857667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26572322932474054323905111 39858484398711081485857667)
                ·
                  refine ⟨59787726598066622228786501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39858484398711081485857667 59787726598066622228786501)
                  ·
                    refine ⟨11210198737137491667897469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59787726598066622228786501 11210198737137491667897469)
                    ·
                      refine ⟨4203824526426559375461551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11210198737137491667897469 4203824526426559375461551)
                      ·
                        rfl

theorem cell23_8186919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_8186919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186919 prefixEnd_8186919 := by exact prefixLift 8186919
  have htrace : WordTrace (prefixWord ++ tailWord_8186919) baseStart_8186919 baseEnd_8186919 := by
    simpa [prefixWord, tailWord_8186919, baseEnd_8186919] using wordTrace_append hprefix tailTrace_8186919
  have hstable : (prefixWord ++ tailWord_8186919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186919).length < 2 ^ (prefixWord ++ tailWord_8186919).sum := by decide
  have hdescent : baseEnd_8186919 < baseStart_8186919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186926 : List Nat := [4, 1, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_8186926 : Nat := 118140960795 + 8186926 * 2 ^ 59
def prefixEnd_8186926 : Nat := 4983230072969 + 3 ^ 40 * 8186926 * 2
def baseEnd_8186926 : Nat := 1401276040263713616024673

theorem tailTrace_8186926 : CollatzResearch.WordTrace tailWord_8186926 prefixEnd_8186926 1401276040263713616024673 := by
  unfold tailWord_8186926
  simp only [CollatzResearch.WordTrace]
  refine ⟨37325215292271599061034579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199067814892115194992184421 37325215292271599061034579)
  ·
    refine ⟨55987822938407398591551869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37325215292271599061034579 55987822938407398591551869)
    ·
      refine ⟨20995433601902774471831951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55987822938407398591551869 20995433601902774471831951)
      ·
        refine ⟨31493150402854161707747927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20995433601902774471831951 31493150402854161707747927)
        ·
          refine ⟨47239725604281242561621891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31493150402854161707747927 47239725604281242561621891)
          ·
            refine ⟨70859588406421863842432837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47239725604281242561621891 70859588406421863842432837)
            ·
              refine ⟨13286172826204099470456157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70859588406421863842432837 13286172826204099470456157)
              ·
                refine ⟨4982314809826537301421059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13286172826204099470456157 4982314809826537301421059)
                ·
                  refine ⟨7473472214739805952131589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982314809826537301421059 7473472214739805952131589)
                  ·
                    refine ⟨1401276040263713616024673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7473472214739805952131589 1401276040263713616024673)
                    ·
                      rfl

theorem cell23_8186926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_8186926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186926 prefixEnd_8186926 := by exact prefixLift 8186926
  have htrace : WordTrace (prefixWord ++ tailWord_8186926) baseStart_8186926 baseEnd_8186926 := by
    simpa [prefixWord, tailWord_8186926, baseEnd_8186926] using wordTrace_append hprefix tailTrace_8186926
  have hstable : (prefixWord ++ tailWord_8186926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186926).length < 2 ^ (prefixWord ++ tailWord_8186926).sum := by decide
  have hdescent : baseEnd_8186926 < baseStart_8186926 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186942 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_8186942 : Nat := 118140960795 + 8186942 * 2 ^ 59
def prefixEnd_8186942 : Nat := 4983230072969 + 3 ^ 40 * 8186942 * 2
def baseEnd_8186942 : Nat := 4203836336481612785473945

theorem tailTrace_8186942 : CollatzResearch.WordTrace tailWord_8186942 prefixEnd_8186942 4203836336481612785473945 := by
  unfold tailWord_8186942
  simp only [CollatzResearch.WordTrace]
  refine ⟨37325288238264353402607385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199068203937409884813906053 37325288238264353402607385)
  ·
    refine ⟨27993966178698265051955539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37325288238264353402607385 27993966178698265051955539)
    ·
      refine ⟨41990949268047397577933309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27993966178698265051955539 41990949268047397577933309)
      ·
        refine ⟨15746605975517774091724991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41990949268047397577933309 15746605975517774091724991)
        ·
          refine ⟨23619908963276661137587487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15746605975517774091724991 23619908963276661137587487)
          ·
            refine ⟨35429863444914991706381231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23619908963276661137587487 35429863444914991706381231)
            ·
              refine ⟨53144795167372487559571847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35429863444914991706381231 53144795167372487559571847)
              ·
                refine ⟨79717192751058731339357771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53144795167372487559571847 79717192751058731339357771)
                ·
                  refine ⟨119575789126588097009036657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79717192751058731339357771 119575789126588097009036657)
                  ·
                    refine ⟨89681841844941072756777493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119575789126588097009036657 89681841844941072756777493)
                    ·
                      refine ⟨4203836336481612785473945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89681841844941072756777493 4203836336481612785473945)
                      ·
                        rfl

theorem cell23_8186942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_8186942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186942 prefixEnd_8186942 := by exact prefixLift 8186942
  have htrace : WordTrace (prefixWord ++ tailWord_8186942) baseStart_8186942 baseEnd_8186942 := by
    simpa [prefixWord, tailWord_8186942, baseEnd_8186942] using wordTrace_append hprefix tailTrace_8186942
  have hstable : (prefixWord ++ tailWord_8186942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186942).length < 2 ^ (prefixWord ++ tailWord_8186942).sum := by decide
  have hdescent : baseEnd_8186942 < baseStart_8186942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186975 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 5]
def baseStart_8186975 : Nat := 118140960795 + 8186975 * 2 ^ 59
def prefixEnd_8186975 : Nat := 4983230072969 + 3 ^ 40 * 8186975 * 2
def baseEnd_8186975 : Nat := 4203853281343211156361293

theorem tailTrace_8186975 : CollatzResearch.WordTrace tailWord_8186975 prefixEnd_8186975 4203853281343211156361293 := by
  unfold tailWord_8186975
  simp only [CollatzResearch.WordTrace]
  refine ⟨298603509514995273856810379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199069006343330182571206919 298603509514995273856810379)
  ·
    refine ⟨447905264272492910785215569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298603509514995273856810379 447905264272492910785215569)
    ·
      refine ⟨335928948204369683088911677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447905264272492910785215569 335928948204369683088911677)
      ·
        refine ⟨125973355576638631158341879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335928948204369683088911677 125973355576638631158341879)
        ·
          refine ⟨188960033364957946737512819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125973355576638631158341879 188960033364957946737512819)
          ·
            refine ⟨283440050047436920106269229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188960033364957946737512819 283440050047436920106269229)
            ·
              refine ⟨106290018767788845039850961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283440050047436920106269229 106290018767788845039850961)
              ·
                refine ⟨79717514075841633779888221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106290018767788845039850961 79717514075841633779888221)
                ·
                  refine ⟨29894067778440612667458083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79717514075841633779888221 29894067778440612667458083)
                  ·
                    refine ⟨44841101667660919001187125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29894067778440612667458083 44841101667660919001187125)
                    ·
                      refine ⟨4203853281343211156361293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44841101667660919001187125 4203853281343211156361293)
                      ·
                        rfl

theorem cell23_8186975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_8186975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186975 prefixEnd_8186975 := by exact prefixLift 8186975
  have htrace : WordTrace (prefixWord ++ tailWord_8186975) baseStart_8186975 baseEnd_8186975 := by
    simpa [prefixWord, tailWord_8186975, baseEnd_8186975] using wordTrace_append hprefix tailTrace_8186975
  have hstable : (prefixWord ++ tailWord_8186975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186975).length < 2 ^ (prefixWord ++ tailWord_8186975).sum := by decide
  have hdescent : baseEnd_8186975 < baseStart_8186975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186983 : List Nat := [1, 1, 5, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_8186983 : Nat := 118140960795 + 8186983 * 2 ^ 59
def prefixEnd_8186983 : Nat := 4983230072969 + 3 ^ 40 * 8186983 * 2
def baseEnd_8186983 : Nat := 4203857389188447125061257

theorem tailTrace_8186983 : CollatzResearch.WordTrace tailWord_8186983 prefixEnd_8186983 4203857389188447125061257 := by
  unfold tailWord_8186983
  simp only [CollatzResearch.WordTrace]
  refine ⟨298603801298966291223101603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199069200865977527482067735 298603801298966291223101603)
  ·
    refine ⟨447905701948449436834652405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298603801298966291223101603 447905701948449436834652405)
    ·
      refine ⟨41991159557667134703248663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 447905701948449436834652405 41991159557667134703248663)
      ·
        refine ⟨62986739336500702054872995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41991159557667134703248663 62986739336500702054872995)
        ·
          refine ⟨94480109004751053082309493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62986739336500702054872995 94480109004751053082309493)
          ·
            refine ⟨8857510219195411226466515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94480109004751053082309493 8857510219195411226466515)
            ·
              refine ⟨13286265328793116839699773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8857510219195411226466515 13286265328793116839699773)
              ·
                refine ⟨4982349498297418814887415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13286265328793116839699773 4982349498297418814887415)
                ·
                  refine ⟨7473524247446128222331123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982349498297418814887415 7473524247446128222331123)
                  ·
                    refine ⟨11210286371169192333496685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7473524247446128222331123 11210286371169192333496685)
                    ·
                      refine ⟨4203857389188447125061257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11210286371169192333496685 4203857389188447125061257)
                      ·
                        rfl

theorem cell23_8186983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_8186983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186983 prefixEnd_8186983 := by exact prefixLift 8186983
  have htrace : WordTrace (prefixWord ++ tailWord_8186983) baseStart_8186983 baseEnd_8186983 := by
    simpa [prefixWord, tailWord_8186983, baseEnd_8186983] using wordTrace_append hprefix tailTrace_8186983
  have hstable : (prefixWord ++ tailWord_8186983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186983).length < 2 ^ (prefixWord ++ tailWord_8186983).sum := by decide
  have hdescent : baseEnd_8186983 < baseStart_8186983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186989 : List Nat := [1, 5, 1, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_8186989 : Nat := 118140960795 + 8186989 * 2 ^ 59
def prefixEnd_8186989 : Nat := 4983230072969 + 3 ^ 40 * 8186989 * 2
def baseEnd_8186989 : Nat := 4203860470072374101586229

theorem tailTrace_8186989 : CollatzResearch.WordTrace tailWord_8186989 prefixEnd_8186989 4203860470072374101586229 := by
  unfold tailWord_8186989
  simp only [CollatzResearch.WordTrace]
  refine ⟨298604020136944554247820021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199069346757963036165213347 298604020136944554247820021)
  ·
    refine ⟨27994126887838551960733127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298604020136944554247820021 27994126887838551960733127)
    ·
      refine ⟨41991190331757827941099691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27994126887838551960733127 41991190331757827941099691)
      ·
        refine ⟨62986785497636741911649537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41991190331757827941099691 62986785497636741911649537)
        ·
          refine ⟨47240089123227556433737153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62986785497636741911649537 47240089123227556433737153)
          ·
            refine ⟨35430066842420667325302865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47240089123227556433737153 35430066842420667325302865)
            ·
              refine ⟨26572550131815500493977149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35430066842420667325302865 26572550131815500493977149)
              ·
                refine ⟨9964706299430812685241431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26572550131815500493977149 9964706299430812685241431)
                ·
                  refine ⟨14947059449146219027862147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9964706299430812685241431 14947059449146219027862147)
                  ·
                    refine ⟨22420589173719328541793221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14947059449146219027862147 22420589173719328541793221)
                    ·
                      refine ⟨4203860470072374101586229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22420589173719328541793221 4203860470072374101586229)
                      ·
                        rfl

theorem cell23_8186989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_8186989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186989 prefixEnd_8186989 := by exact prefixLift 8186989
  have htrace : WordTrace (prefixWord ++ tailWord_8186989) baseStart_8186989 baseEnd_8186989 := by
    simpa [prefixWord, tailWord_8186989, baseEnd_8186989] using wordTrace_append hprefix tailTrace_8186989
  have hstable : (prefixWord ++ tailWord_8186989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186989).length < 2 ^ (prefixWord ++ tailWord_8186989).sum := by decide
  have hdescent : baseEnd_8186989 < baseStart_8186989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8186992 : List Nat := [2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 5]
def baseStart_8186992 : Nat := 118140960795 + 8186992 * 2 ^ 59
def prefixEnd_8186992 : Nat := 4983230072969 + 3 ^ 40 * 8186992 * 2
def baseEnd_8186992 : Nat := 4203862010514337589848715

theorem tailTrace_8186992 : CollatzResearch.WordTrace tailWord_8186992 prefixEnd_8186992 4203862010514337589848715 := by
  unfold tailWord_8186992
  simp only [CollatzResearch.WordTrace]
  refine ⟨149302064777966842880089615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199069419703955790506786153 149302064777966842880089615)
  ·
    refine ⟨223953097166950264320134423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149302064777966842880089615 223953097166950264320134423)
    ·
      refine ⟨335929645750425396480201635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223953097166950264320134423 335929645750425396480201635)
      ·
        refine ⟨503894468625638094720302453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335929645750425396480201635 503894468625638094720302453)
        ·
          refine ⟨47240106433653571380028355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 503894468625638094720302453 47240106433653571380028355)
          ·
            refine ⟨70860159650480357070042533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47240106433653571380028355 70860159650480357070042533)
            ·
              refine ⟨13286279934465066950632975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70860159650480357070042533 13286279934465066950632975)
              ·
                refine ⟨19929419901697600425949463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13286279934465066950632975 19929419901697600425949463)
                ·
                  refine ⟨29894129852546400638924195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19929419901697600425949463 29894129852546400638924195)
                  ·
                    refine ⟨44841194778819600958386293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29894129852546400638924195 44841194778819600958386293)
                    ·
                      refine ⟨4203862010514337589848715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44841194778819600958386293 4203862010514337589848715)
                      ·
                        rfl

theorem cell23_8186992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 5].length) (baseStart_8186992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8186992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8186992 prefixEnd_8186992 := by exact prefixLift 8186992
  have htrace : WordTrace (prefixWord ++ tailWord_8186992) baseStart_8186992 baseEnd_8186992 := by
    simpa [prefixWord, tailWord_8186992, baseEnd_8186992] using wordTrace_append hprefix tailTrace_8186992
  have hstable : (prefixWord ++ tailWord_8186992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8186992).length < 2 ^ (prefixWord ++ tailWord_8186992).sum := by decide
  have hdescent : baseEnd_8186992 < baseStart_8186992 := by decide
  rcases family_descends (prefixWord ++ tailWord_8186992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187012 : List Nat := [2, 3, 2, 1, 2, 3, 2, 8]
def baseStart_8187012 : Nat := 118140960795 + 8187012 * 2 ^ 59
def prefixEnd_8187012 : Nat := 4983230072969 + 3 ^ 40 * 8187012 * 2
def baseEnd_8187012 : Nat := 155698973338052870799949

theorem tailTrace_8187012 : CollatzResearch.WordTrace tailWord_8187012 prefixEnd_8187012 155698973338052870799949 := by
  unfold tailWord_8187012
  simp only [CollatzResearch.WordTrace]
  refine ⟨149302429507930614587953645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199069906010574152783938193 149302429507930614587953645)
  ·
    refine ⟨55988411065473980470482617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149302429507930614587953645 55988411065473980470482617)
    ·
      refine ⟨41991308299105485352861963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55988411065473980470482617 41991308299105485352861963)
      ·
        refine ⟨62986962448658228029292945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41991308299105485352861963 62986962448658228029292945)
        ·
          refine ⟨47240221836493671021969709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62986962448658228029292945 47240221836493671021969709)
          ·
            refine ⟨17715083188685126633238641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47240221836493671021969709 17715083188685126633238641)
            ·
              refine ⟨13286312391513844974928981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17715083188685126633238641 13286312391513844974928981)
              ·
                refine ⟨155698973338052870799949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13286312391513844974928981 155698973338052870799949)
                ·
                  rfl

theorem cell23_8187012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 8].length) (baseStart_8187012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187012 prefixEnd_8187012 := by exact prefixLift 8187012
  have htrace : WordTrace (prefixWord ++ tailWord_8187012) baseStart_8187012 baseEnd_8187012 := by
    simpa [prefixWord, tailWord_8187012, baseEnd_8187012] using wordTrace_append hprefix tailTrace_8187012
  have hstable : (prefixWord ++ tailWord_8187012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187012).length < 2 ^ (prefixWord ++ tailWord_8187012).sum := by decide
  have hdescent : baseEnd_8187012 < baseStart_8187012 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187015 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_8187015 : Nat := 118140960795 + 8187015 * 2 ^ 59
def prefixEnd_8187015 : Nat := 4983230072969 + 3 ^ 40 * 8187015 * 2
def baseEnd_8187015 : Nat := 4203873820569390999861109

theorem tailTrace_8187015 : CollatzResearch.WordTrace tailWord_8187015 prefixEnd_8187015 4203873820569390999861109 := by
  unfold tailWord_8187015
  simp only [CollatzResearch.WordTrace]
  refine ⟨298604968434850360688266499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199069978956566907125510999 298604968434850360688266499)
  ·
    refine ⟨447907452652275541032399749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298604968434850360688266499 447907452652275541032399749)
    ·
      refine ⟨83982647372301663943574953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 447907452652275541032399749 83982647372301663943574953)
      ·
        refine ⟨62986985529226247957681215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83982647372301663943574953 62986985529226247957681215)
        ·
          refine ⟨94480478293839371936521823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62986985529226247957681215 94480478293839371936521823)
          ·
            refine ⟨141720717440759057904782735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94480478293839371936521823 141720717440759057904782735)
            ·
              refine ⟨212581076161138586857174103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141720717440759057904782735 212581076161138586857174103)
              ·
                refine ⟨318871614241707880285761155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212581076161138586857174103 318871614241707880285761155)
                ·
                  refine ⟨478307421362561820428641733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318871614241707880285761155 478307421362561820428641733)
                  ·
                    refine ⟨89682641505480341330370325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 478307421362561820428641733 89682641505480341330370325)
                    ·
                      refine ⟨4203873820569390999861109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89682641505480341330370325 4203873820569390999861109)
                      ·
                        rfl

theorem cell23_8187015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_8187015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187015 prefixEnd_8187015 := by exact prefixLift 8187015
  have htrace : WordTrace (prefixWord ++ tailWord_8187015) baseStart_8187015 baseEnd_8187015 := by
    simpa [prefixWord, tailWord_8187015, baseEnd_8187015] using wordTrace_append hprefix tailTrace_8187015
  have hstable : (prefixWord ++ tailWord_8187015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187015).length < 2 ^ (prefixWord ++ tailWord_8187015).sum := by decide
  have hdescent : baseEnd_8187015 < baseStart_8187015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187016 : List Nat := [2, 1, 3, 4, 2, 1, 1, 3, 2, 4]
def baseStart_8187016 : Nat := 118140960795 + 8187016 * 2 ^ 59
def prefixEnd_8187016 : Nat := 4983230072969 + 3 ^ 40 * 8187016 * 2
def baseEnd_8187016 : Nat := 1401291444683348498649535

theorem tailTrace_8187016 : CollatzResearch.WordTrace tailWord_8187016 prefixEnd_8187016 1401291444683348498649535 := by
  unfold tailWord_8187016
  simp only [CollatzResearch.WordTrace]
  refine ⟨149302502453923368929526451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199070003271897825239368601 149302502453923368929526451)
  ·
    refine ⟨223953753680885053394289677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149302502453923368929526451 223953753680885053394289677)
    ·
      refine ⟨83982657630331895022858629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223953753680885053394289677 83982657630331895022858629)
      ·
        refine ⟨15746748305687230316785993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83982657630331895022858629 15746748305687230316785993)
        ·
          refine ⟨11810061229265422737589495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15746748305687230316785993 11810061229265422737589495)
          ·
            refine ⟨17715091843898134106384243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11810061229265422737589495 17715091843898134106384243)
            ·
              refine ⟨26572637765847201159576365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17715091843898134106384243 26572637765847201159576365)
              ·
                refine ⟨9964739162192700434841137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26572637765847201159576365 9964739162192700434841137)
                ·
                  refine ⟨7473554371644525326130853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9964739162192700434841137 7473554371644525326130853)
                  ·
                    refine ⟨1401291444683348498649535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7473554371644525326130853 1401291444683348498649535)
                    ·
                      rfl

theorem cell23_8187016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_8187016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187016 prefixEnd_8187016 := by exact prefixLift 8187016
  have htrace : WordTrace (prefixWord ++ tailWord_8187016) baseStart_8187016 baseEnd_8187016 := by
    simpa [prefixWord, tailWord_8187016, baseEnd_8187016] using wordTrace_append hprefix tailTrace_8187016
  have hstable : (prefixWord ++ tailWord_8187016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187016).length < 2 ^ (prefixWord ++ tailWord_8187016).sum := by decide
  have hdescent : baseEnd_8187016 < baseStart_8187016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187026 : List Nat := [3, 2, 3, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_8187026 : Nat := 118140960795 + 8187026 * 2 ^ 59
def prefixEnd_8187026 : Nat := 4983230072969 + 3 ^ 40 * 8187026 * 2
def baseEnd_8187026 : Nat := 4203879468856590456823559

theorem tailTrace_8187026 : CollatzResearch.WordTrace tailWord_8187026 prefixEnd_8187026 4203879468856590456823559 := by
  unfold tailWord_8187026
  simp only [CollatzResearch.WordTrace]
  refine ⟨74651342409452627391729233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199070246425207006377944621 74651342409452627391729233)
  ·
    refine ⟨55988506807089470543796925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74651342409452627391729233 55988506807089470543796925)
    ·
      refine ⟨20995690052658551453923847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55988506807089470543796925 20995690052658551453923847)
      ·
        refine ⟨31493535078987827180885771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20995690052658551453923847 31493535078987827180885771)
        ·
          refine ⟨47240302618481740771328657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31493535078987827180885771 47240302618481740771328657)
          ·
            refine ⟨35430226963861305578496493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47240302618481740771328657 35430226963861305578496493)
            ·
              refine ⟨13286335111447989591936185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35430226963861305578496493 13286335111447989591936185)
              ·
                refine ⟨9964751333585992193952139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13286335111447989591936185 9964751333585992193952139)
                ·
                  refine ⟨14947127000378988290928209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9964751333585992193952139 14947127000378988290928209)
                  ·
                    refine ⟨11210345250284241218196157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14947127000378988290928209 11210345250284241218196157)
                    ·
                      refine ⟨4203879468856590456823559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11210345250284241218196157 4203879468856590456823559)
                      ·
                        rfl

theorem cell23_8187026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_8187026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187026 prefixEnd_8187026 := by exact prefixLift 8187026
  have htrace : WordTrace (prefixWord ++ tailWord_8187026) baseStart_8187026 baseEnd_8187026 := by
    simpa [prefixWord, tailWord_8187026, baseEnd_8187026] using wordTrace_append hprefix tailTrace_8187026
  have hstable : (prefixWord ++ tailWord_8187026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187026).length < 2 ^ (prefixWord ++ tailWord_8187026).sum := by decide
  have hdescent : baseEnd_8187026 < baseStart_8187026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187057 : List Nat := [1, 2, 2, 5, 1, 3, 2, 2, 1, 2, 2]
def baseStart_8187057 : Nat := 118140960795 + 8187057 * 2 ^ 59
def prefixEnd_8187057 : Nat := 4983230072969 + 3 ^ 40 * 8187057 * 2
def baseEnd_8187057 : Nat := 4203895386756879835535917

theorem tailTrace_8187057 : CollatzResearch.WordTrace tailWord_8187057 prefixEnd_8187057 4203895386756879835535917 := by
  unfold tailWord_8187057
  simp only [CollatzResearch.WordTrace]
  refine ⟨298606500300698201861295425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199071000200465467907530283 298606500300698201861295425)
  ·
    refine ⟨223954875225523651395971569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298606500300698201861295425 223954875225523651395971569)
    ·
      refine ⟨167966156419142738546978677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223954875225523651395971569 167966156419142738546978677)
      ·
        refine ⟨15746827164294631738779251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167966156419142738546978677 15746827164294631738779251)
        ·
          refine ⟨23620240746441947608168877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15746827164294631738779251 23620240746441947608168877)
          ·
            refine ⟨8857590279915730353063329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23620240746441947608168877 8857590279915730353063329)
            ·
              refine ⟨6643192709936797764797497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8857590279915730353063329 6643192709936797764797497)
              ·
                refine ⟨4982394532452598323598123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6643192709936797764797497 4982394532452598323598123)
                ·
                  refine ⟨7473591798678897485397185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982394532452598323598123 7473591798678897485397185)
                  ·
                    refine ⟨5605193849009173114047889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7473591798678897485397185 5605193849009173114047889)
                    ·
                      refine ⟨4203895386756879835535917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5605193849009173114047889 4203895386756879835535917)
                      ·
                        rfl

theorem cell23_8187057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_8187057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187057 prefixEnd_8187057 := by exact prefixLift 8187057
  have htrace : WordTrace (prefixWord ++ tailWord_8187057) baseStart_8187057 baseEnd_8187057 := by
    simpa [prefixWord, tailWord_8187057, baseEnd_8187057] using wordTrace_append hprefix tailTrace_8187057
  have hstable : (prefixWord ++ tailWord_8187057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187057).length < 2 ^ (prefixWord ++ tailWord_8187057).sum := by decide
  have hdescent : baseEnd_8187057 < baseStart_8187057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187073 : List Nat := [1, 2, 6, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_8187073 : Nat := 118140960795 + 8187073 * 2 ^ 59
def prefixEnd_8187073 : Nat := 4983230072969 + 3 ^ 40 * 8187073 * 2
def baseEnd_8187073 : Nat := 4203903602447351772935843

theorem tailTrace_8187073 : CollatzResearch.WordTrace tailWord_8187073 prefixEnd_8187073 4203903602447351772935843 := by
  unfold tailWord_8187073
  simp only [CollatzResearch.WordTrace]
  refine ⟨298607083868640236593877873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199071389245760157729251915 298607083868640236593877873)
  ·
    refine ⟨223955312901480177445408405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298607083868640236593877873 223955312901480177445408405)
    ·
      refine ⟨10497905292256883317753519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 223955312901480177445408405 10497905292256883317753519)
      ·
        refine ⟨15746857938385324976630279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10497905292256883317753519 15746857938385324976630279)
        ·
          refine ⟨23620286907577987464945419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15746857938385324976630279 23620286907577987464945419)
          ·
            refine ⟨35430430361366981197418129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23620286907577987464945419 35430430361366981197418129)
            ·
              refine ⟨26572822771025235898063597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35430430361366981197418129 26572822771025235898063597)
              ·
                refine ⟨9964808539134463461773849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26572822771025235898063597 9964808539134463461773849)
                ·
                  refine ⟨7473606404350847596330387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9964808539134463461773849 7473606404350847596330387)
                  ·
                    refine ⟨11210409606526271394495581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7473606404350847596330387 11210409606526271394495581)
                    ·
                      refine ⟨4203903602447351772935843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11210409606526271394495581 4203903602447351772935843)
                      ·
                        rfl

theorem cell23_8187073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_8187073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187073 prefixEnd_8187073 := by exact prefixLift 8187073
  have htrace : WordTrace (prefixWord ++ tailWord_8187073) baseStart_8187073 baseEnd_8187073 := by
    simpa [prefixWord, tailWord_8187073, baseEnd_8187073] using wordTrace_append hprefix tailTrace_8187073
  have hstable : (prefixWord ++ tailWord_8187073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187073).length < 2 ^ (prefixWord ++ tailWord_8187073).sum := by decide
  have hdescent : baseEnd_8187073 < baseStart_8187073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187119 : List Nat := [1, 1, 2, 1, 7, 1, 2, 1, 7]
def baseStart_8187119 : Nat := 118140960795 + 8187119 * 2 ^ 59
def prefixEnd_8187119 : Nat := 4983230072969 + 3 ^ 40 * 8187119 * 2
def baseEnd_8187119 : Nat := 467103024728606510328959

theorem tailTrace_8187119 : CollatzResearch.WordTrace tailWord_8187119 prefixEnd_8187119 467103024728606510328959 := by
  unfold tailWord_8187119
  simp only [CollatzResearch.WordTrace]
  refine ⟨298608761626473586450052411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199072507750982390966701607 298608761626473586450052411)
  ·
    refine ⟨447913142439710379675078617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298608761626473586450052411 447913142439710379675078617)
    ·
      refine ⟨335934856829782784756308963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447913142439710379675078617 335934856829782784756308963)
      ·
        refine ⟨503902285244674177134463445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335934856829782784756308963 503902285244674177134463445)
        ·
          refine ⟨11810209810422051026588987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 503902285244674177134463445 11810209810422051026588987)
          ·
            refine ⟨17715314715633076539883481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11810209810422051026588987 17715314715633076539883481)
            ·
              refine ⟨13286486036724807404912611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17715314715633076539883481 13286486036724807404912611)
              ·
                refine ⟨19929729055087211107368917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13286486036724807404912611 19929729055087211107368917)
                ·
                  refine ⟨467103024728606510328959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19929729055087211107368917 467103024728606510328959)
                  ·
                    rfl

theorem cell23_8187119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 1, 7].length) (baseStart_8187119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187119 prefixEnd_8187119 := by exact prefixLift 8187119
  have htrace : WordTrace (prefixWord ++ tailWord_8187119) baseStart_8187119 baseEnd_8187119 := by
    simpa [prefixWord, tailWord_8187119, baseEnd_8187119] using wordTrace_append hprefix tailTrace_8187119
  have hstable : (prefixWord ++ tailWord_8187119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187119).length < 2 ^ (prefixWord ++ tailWord_8187119).sum := by decide
  have hdescent : baseEnd_8187119 < baseStart_8187119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187124 : List Nat := [2, 6, 1, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_8187124 : Nat := 118140960795 + 8187124 * 2 ^ 59
def prefixEnd_8187124 : Nat := 4983230072969 + 3 ^ 40 * 8187124 * 2
def baseEnd_8187124 : Nat := 4203929789960731073398109

theorem tailTrace_8187124 : CollatzResearch.WordTrace tailWord_8187124 prefixEnd_8187124 4203929789960731073398109 := by
  unfold tailWord_8187124
  simp only [CollatzResearch.WordTrace]
  refine ⟨149304471995727736151992213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199072629327636981535989617 149304471995727736151992213)
  ·
    refine ⟨6998647124799737632124635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149304471995727736151992213 6998647124799737632124635)
    ·
      refine ⟨10497970687199606448186953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6998647124799737632124635 10497970687199606448186953)
      ·
        refine ⟨7873478015399704836140215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10497970687199606448186953 7873478015399704836140215)
        ·
          refine ⟨11810217023099557254210323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7873478015399704836140215 11810217023099557254210323)
          ·
            refine ⟨17715325534649335881315485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11810217023099557254210323 17715325534649335881315485)
            ·
              refine ⟨6643247075493500955493307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17715325534649335881315485 6643247075493500955493307)
              ·
                refine ⟨9964870613240251433239961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6643247075493500955493307 9964870613240251433239961)
                ·
                  refine ⟨7473652959930188574929971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9964870613240251433239961 7473652959930188574929971)
                  ·
                    refine ⟨11210479439895282862394957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7473652959930188574929971 11210479439895282862394957)
                    ·
                      refine ⟨4203929789960731073398109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11210479439895282862394957 4203929789960731073398109)
                      ·
                        rfl

theorem cell23_8187124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_8187124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187124 prefixEnd_8187124 := by exact prefixLift 8187124
  have htrace : WordTrace (prefixWord ++ tailWord_8187124) baseStart_8187124 baseEnd_8187124 := by
    simpa [prefixWord, tailWord_8187124, baseEnd_8187124] using wordTrace_append hprefix tailTrace_8187124
  have hstable : (prefixWord ++ tailWord_8187124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187124).length < 2 ^ (prefixWord ++ tailWord_8187124).sum := by decide
  have hdescent : baseEnd_8187124 < baseStart_8187124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187259 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 4]
def baseStart_8187259 : Nat := 118140960795 + 8187259 * 2 ^ 59
def prefixEnd_8187259 : Nat := 4983230072969 + 3 ^ 40 * 8187259 * 2
def baseEnd_8187259 : Nat := 4203999109849088045209987

theorem tailTrace_8187259 : CollatzResearch.WordTrace tailWord_8187259 prefixEnd_8187259 4203999109849088045209987 := by
  unfold tailWord_8187259
  simp only [CollatzResearch.WordTrace]
  refine ⟨298613867845966390360148831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199075911897310926906765887 298613867845966390360148831)
  ·
    refine ⟨447920801768949585540223247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298613867845966390360148831 447920801768949585540223247)
    ·
      refine ⟨671881202653424378310334871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447920801768949585540223247 671881202653424378310334871)
      ·
        refine ⟨1007821803980136567465502307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671881202653424378310334871 1007821803980136567465502307)
        ·
          refine ⟨1511732705970204851198253461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007821803980136567465502307 1511732705970204851198253461)
          ·
            refine ⟨70862470592353352399918131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1511732705970204851198253461 70862470592353352399918131)
            ·
              refine ⟨106293705888530028599877197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70862470592353352399918131 106293705888530028599877197)
              ·
                refine ⟨39860139708198760724953949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106293705888530028599877197 39860139708198760724953949)
                ·
                  refine ⟨14947552390574535271857731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39860139708198760724953949 14947552390574535271857731)
                  ·
                    refine ⟨22421328585861802907786597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14947552390574535271857731 22421328585861802907786597)
                    ·
                      refine ⟨4203999109849088045209987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22421328585861802907786597 4203999109849088045209987)
                      ·
                        rfl

theorem cell23_8187259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 4].length) (baseStart_8187259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187259 prefixEnd_8187259 := by exact prefixLift 8187259
  have htrace : WordTrace (prefixWord ++ tailWord_8187259) baseStart_8187259 baseEnd_8187259 := by
    simpa [prefixWord, tailWord_8187259, baseEnd_8187259] using wordTrace_append hprefix tailTrace_8187259
  have hstable : (prefixWord ++ tailWord_8187259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187259).length < 2 ^ (prefixWord ++ tailWord_8187259).sum := by decide
  have hdescent : baseEnd_8187259 < baseStart_8187259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187269 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 1, 6]
def baseStart_8187269 : Nat := 118140960795 + 8187269 * 2 ^ 59
def prefixEnd_8187269 : Nat := 4983230072969 + 3 ^ 40 * 8187269 * 2
def baseEnd_8187269 : Nat := 1401334748218544335361647

theorem tailTrace_8187269 : CollatzResearch.WordTrace tailWord_8187269 prefixEnd_8187269 1401334748218544335361647 := by
  unfold tailWord_8187269
  simp only [CollatzResearch.WordTrace]
  refine ⟨298614232575930162068012861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199076155050620108045341907 298614232575930162068012861)
  ·
    refine ⟨111980337215973810775504823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298614232575930162068012861 111980337215973810775504823)
    ·
      refine ⟨167970505823960716163257235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111980337215973810775504823 167970505823960716163257235)
      ·
        refine ⟨251955758735941074244885853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167970505823960716163257235 251955758735941074244885853)
        ·
          refine ⟨94483409525977902841832195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251955758735941074244885853 94483409525977902841832195)
          ·
            refine ⟨141725114288966854262748293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94483409525977902841832195 141725114288966854262748293)
            ·
              refine ⟨26573458929181285174265305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141725114288966854262748293 26573458929181285174265305)
              ·
                refine ⟨19930094196885963880698979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26573458929181285174265305 19930094196885963880698979)
                ·
                  refine ⟨29895141295328945821048469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19930094196885963880698979 29895141295328945821048469)
                  ·
                    refine ⟨1401334748218544335361647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29895141295328945821048469 1401334748218544335361647)
                    ·
                      rfl

theorem cell23_8187269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_8187269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187269 prefixEnd_8187269 := by exact prefixLift 8187269
  have htrace : WordTrace (prefixWord ++ tailWord_8187269) baseStart_8187269 baseEnd_8187269 := by
    simpa [prefixWord, tailWord_8187269, baseEnd_8187269] using wordTrace_append hprefix tailTrace_8187269
  have hstable : (prefixWord ++ tailWord_8187269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187269).length < 2 ^ (prefixWord ++ tailWord_8187269).sum := by decide
  have hdescent : baseEnd_8187269 < baseStart_8187269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187276 : List Nat := [2, 2, 1, 2, 1, 3, 3, 3, 1, 1, 4]
def baseStart_8187276 : Nat := 118140960795 + 8187276 * 2 ^ 59
def prefixEnd_8187276 : Nat := 4983230072969 + 3 ^ 40 * 8187276 * 2
def baseEnd_8187276 : Nat := 4204007839020214478697409

theorem tailTrace_8187276 : CollatzResearch.WordTrace tailWord_8187276 prefixEnd_8187276 4204007839020214478697409 := by
  unfold tailWord_8187276
  simp only [CollatzResearch.WordTrace]
  refine ⟨149307243943452401131758841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199076325257936534842345121 149307243943452401131758841)
  ·
    refine ⟨111980432957589300848819131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149307243943452401131758841 111980432957589300848819131)
    ·
      refine ⟨167970649436383951273228697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111980432957589300848819131 167970649436383951273228697)
      ·
        refine ⟨125977987077287963454921523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167970649436383951273228697 125977987077287963454921523)
        ·
          refine ⟨188966980615931945182382285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125977987077287963454921523 188966980615931945182382285)
          ·
            refine ⟨70862617730974479443393357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188966980615931945182382285 70862617730974479443393357)
            ·
              refine ⟨26573481649115429791272509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70862617730974479443393357 26573481649115429791272509)
              ·
                refine ⟨9965055618418286171727191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26573481649115429791272509 9965055618418286171727191)
                ·
                  refine ⟨14947583427627429257590787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9965055618418286171727191 14947583427627429257590787)
                  ·
                    refine ⟨22421375141441143886386181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14947583427627429257590787 22421375141441143886386181)
                    ·
                      refine ⟨4204007839020214478697409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22421375141441143886386181 4204007839020214478697409)
                      ·
                        rfl

theorem cell23_8187276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_8187276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187276 prefixEnd_8187276 := by exact prefixLift 8187276
  have htrace : WordTrace (prefixWord ++ tailWord_8187276) baseStart_8187276 baseEnd_8187276 := by
    simpa [prefixWord, tailWord_8187276, baseEnd_8187276] using wordTrace_append hprefix tailTrace_8187276
  have hstable : (prefixWord ++ tailWord_8187276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187276).length < 2 ^ (prefixWord ++ tailWord_8187276).sum := by decide
  have hdescent : baseEnd_8187276 < baseStart_8187276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187313 : List Nat := [1, 2, 2, 4, 1, 1, 4, 2, 1, 2, 3]
def baseStart_8187313 : Nat := 118140960795 + 8187313 * 2 ^ 59
def prefixEnd_8187313 : Nat := 4983230072969 + 3 ^ 40 * 8187313 * 2
def baseEnd_8187313 : Nat := 4204026837804430833934739

theorem tailTrace_8187313 : CollatzResearch.WordTrace tailWord_8187313 prefixEnd_8187313 4204026837804430833934739 := by
  unfold tailWord_8187313
  simp only [CollatzResearch.WordTrace]
  refine ⟨298615837387770757582614593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199077224925180505055076395 298615837387770757582614593)
  ·
    refine ⟨223961878040828068186960945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298615837387770757582614593 223961878040828068186960945)
    ·
      refine ⟨167971408530621051140220709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223961878040828068186960945 167971408530621051140220709)
      ·
        refine ⟨31494639099491447088791383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167971408530621051140220709 31494639099491447088791383)
        ·
          refine ⟨47241958649237170633187075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31494639099491447088791383 47241958649237170633187075)
          ·
            refine ⟨70862937973855755949780613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47241958649237170633187075 70862937973855755949780613)
            ·
              refine ⟨13286800870097954240583865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70862937973855755949780613 13286800870097954240583865)
              ·
                refine ⟨9965100652573465680437899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13286800870097954240583865 9965100652573465680437899)
                ·
                  refine ⟨14947650978860198520656849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9965100652573465680437899 14947650978860198520656849)
                  ·
                    refine ⟨11210738234145148890492637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14947650978860198520656849 11210738234145148890492637)
                    ·
                      refine ⟨4204026837804430833934739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11210738234145148890492637 4204026837804430833934739)
                      ·
                        rfl

theorem cell23_8187313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_8187313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187313 prefixEnd_8187313 := by exact prefixLift 8187313
  have htrace : WordTrace (prefixWord ++ tailWord_8187313) baseStart_8187313 baseEnd_8187313 := by
    simpa [prefixWord, tailWord_8187313, baseEnd_8187313] using wordTrace_append hprefix tailTrace_8187313
  have hstable : (prefixWord ++ tailWord_8187313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187313).length < 2 ^ (prefixWord ++ tailWord_8187313).sum := by decide
  have hdescent : baseEnd_8187313 < baseStart_8187313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187326 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_8187326 : Nat := 118140960795 + 8187326 * 2 ^ 59
def prefixEnd_8187326 : Nat := 4983230072969 + 3 ^ 40 * 8187326 * 2
def baseEnd_8187326 : Nat := 4204033513052939283072179

theorem tailTrace_8187326 : CollatzResearch.WordTrace tailWord_8187326 prefixEnd_8187326 4204033513052939283072179 := by
  unfold tailWord_8187326
  simp only [CollatzResearch.WordTrace]
  refine ⟨37327038942090457600354729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199077541024482440535225221 37327038942090457600354729)
  ·
    refine ⟨27995279206567843200266047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37327038942090457600354729 27995279206567843200266047)
    ·
      refine ⟨41992918809851764800399071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27995279206567843200266047 41992918809851764800399071)
      ·
        refine ⟨62989378214777647200598607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41992918809851764800399071 62989378214777647200598607)
        ·
          refine ⟨94484067322166470800897911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62989378214777647200598607 94484067322166470800897911)
          ·
            refine ⟨141726100983249706201346867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94484067322166470800897911 141726100983249706201346867)
            ·
              refine ⟨212589151474874559302020301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141726100983249706201346867 212589151474874559302020301)
              ·
                refine ⟨79720931803077959738257613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212589151474874559302020301 79720931803077959738257613)
                ·
                  refine ⟨29895349426154234901846605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79720931803077959738257613 29895349426154234901846605)
                  ·
                    refine ⟨11210756034807838088192477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29895349426154234901846605 11210756034807838088192477)
                    ·
                      refine ⟨4204033513052939283072179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11210756034807838088192477 4204033513052939283072179)
                      ·
                        rfl

theorem cell23_8187326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_8187326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187326 prefixEnd_8187326 := by exact prefixLift 8187326
  have htrace : WordTrace (prefixWord ++ tailWord_8187326) baseStart_8187326 baseEnd_8187326 := by
    simpa [prefixWord, tailWord_8187326, baseEnd_8187326] using wordTrace_append hprefix tailTrace_8187326
  have hstable : (prefixWord ++ tailWord_8187326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187326).length < 2 ^ (prefixWord ++ tailWord_8187326).sum := by decide
  have hdescent : baseEnd_8187326 < baseStart_8187326 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187359 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 1, 8]
def baseStart_8187359 : Nat := 118140960795 + 8187359 * 2 ^ 59
def prefixEnd_8187359 : Nat := 4983230072969 + 3 ^ 40 * 8187359 * 2
def baseEnd_8187359 : Nat := 1401350152638179217986509

theorem tailTrace_8187359 : CollatzResearch.WordTrace tailWord_8187359 prefixEnd_8187359 1401350152638179217986509 := by
  unfold tailWord_8187359
  simp only [CollatzResearch.WordTrace]
  refine ⟨298617515145604107438789131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199078343430402738292526087 298617515145604107438789131)
  ·
    refine ⟨447926272718406161158183697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298617515145604107438789131 447926272718406161158183697)
    ·
      refine ⟨335944704538804620868637773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447926272718406161158183697 335944704538804620868637773)
      ·
        refine ⟨125979264202051732825739165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335944704538804620868637773 125979264202051732825739165)
        ·
          refine ⟨47242224075769399809652187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125979264202051732825739165 47242224075769399809652187)
          ·
            refine ⟨70863336113654099714478281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47242224075769399809652187 70863336113654099714478281)
            ·
              refine ⟨53147502085240574785858711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70863336113654099714478281 53147502085240574785858711)
              ·
                refine ⟨79721253127860862178788067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53147502085240574785858711 79721253127860862178788067)
                ·
                  refine ⟨119581879691791293268182101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79721253127860862178788067 119581879691791293268182101)
                  ·
                    refine ⟨1401350152638179217986509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119581879691791293268182101 1401350152638179217986509)
                    ·
                      rfl

theorem cell23_8187359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_8187359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187359 prefixEnd_8187359 := by exact prefixLift 8187359
  have htrace : WordTrace (prefixWord ++ tailWord_8187359) baseStart_8187359 baseEnd_8187359 := by
    simpa [prefixWord, tailWord_8187359, baseEnd_8187359] using wordTrace_append hprefix tailTrace_8187359
  have hstable : (prefixWord ++ tailWord_8187359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187359).length < 2 ^ (prefixWord ++ tailWord_8187359).sum := by decide
  have hdescent : baseEnd_8187359 < baseStart_8187359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187370 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_8187370 : Nat := 118140960795 + 8187370 * 2 ^ 59
def prefixEnd_8187370 : Nat := 4983230072969 + 3 ^ 40 * 8187370 * 2
def baseEnd_8187370 : Nat := 4204056106201737110921977

theorem tailTrace_8187370 : CollatzResearch.WordTrace tailWord_8187370 prefixEnd_8187370 4204056106201737110921977 := by
  unfold tailWord_8187370
  simp only [CollatzResearch.WordTrace]
  refine ⟨74654479087141064079359891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199078610899042837544959709 74654479087141064079359891)
  ·
    refine ⟨111981718630711596119039837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74654479087141064079359891 111981718630711596119039837)
    ·
      refine ⟨41993144486516848544639939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111981718630711596119039837 41993144486516848544639939)
      ·
        refine ⟨62989716729775272816959909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41993144486516848544639939 62989716729775272816959909)
        ·
          refine ⟨11810571886832863653179983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62989716729775272816959909 11810571886832863653179983)
          ·
            refine ⟨17715857830249295479769975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11810571886832863653179983 17715857830249295479769975)
            ·
              refine ⟨26573786745373943219654963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17715857830249295479769975 26573786745373943219654963)
              ·
                refine ⟨39860680118060914829482445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26573786745373943219654963 39860680118060914829482445)
                ·
                  refine ⟨14947755044272843061055917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39860680118060914829482445 14947755044272843061055917)
                  ·
                    refine ⟨5605408141602316147895969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14947755044272843061055917 5605408141602316147895969)
                    ·
                      refine ⟨4204056106201737110921977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5605408141602316147895969 4204056106201737110921977)
                      ·
                        rfl

theorem cell23_8187370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_8187370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187370 prefixEnd_8187370 := by exact prefixLift 8187370
  have htrace : WordTrace (prefixWord ++ tailWord_8187370) baseStart_8187370 baseEnd_8187370 := by
    simpa [prefixWord, tailWord_8187370, baseEnd_8187370] using wordTrace_append hprefix tailTrace_8187370
  have hstable : (prefixWord ++ tailWord_8187370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187370).length < 2 ^ (prefixWord ++ tailWord_8187370).sum := by decide
  have hdescent : baseEnd_8187370 < baseStart_8187370 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187379 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 4]
def baseStart_8187379 : Nat := 118140960795 + 8187379 * 2 ^ 59
def prefixEnd_8187379 : Nat := 4983230072969 + 3 ^ 40 * 8187379 * 2
def baseEnd_8187379 : Nat := 4204060727527627575709435

theorem tailTrace_8187379 : CollatzResearch.WordTrace tailWord_8187379 prefixEnd_8187379 4204060727527627575709435 := by
  unfold tailWord_8187379
  simp only [CollatzResearch.WordTrace]
  refine ⟨298618244605531650854517191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199078829737021100569678127 298618244605531650854517191)
  ·
    refine ⟨447927366908297476281775787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298618244605531650854517191 447927366908297476281775787)
    ·
      refine ⟨671891050362446214422663681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447927366908297476281775787 671891050362446214422663681)
      ·
        refine ⟨503918287771834660816997761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671891050362446214422663681 503918287771834660816997761)
        ·
          refine ⟨377938715828875995612748321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503918287771834660816997761 377938715828875995612748321)
          ·
            refine ⟨283454036871656996709561241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377938715828875995612748321 283454036871656996709561241)
            ·
              refine ⟨212590527653742747532170931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283454036871656996709561241 212590527653742747532170931)
              ·
                refine ⟨318885791480614121298256397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212590527653742747532170931 318885791480614121298256397)
                ·
                  refine ⟨119582171805230295486846149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318885791480614121298256397 119582171805230295486846149)
                  ·
                    refine ⟨22421657213480680403783653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119582171805230295486846149 22421657213480680403783653)
                    ·
                      refine ⟨4204060727527627575709435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22421657213480680403783653 4204060727527627575709435)
                      ·
                        rfl

theorem cell23_8187379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_8187379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187379 prefixEnd_8187379 := by exact prefixLift 8187379
  have htrace : WordTrace (prefixWord ++ tailWord_8187379) baseStart_8187379 baseEnd_8187379 := by
    simpa [prefixWord, tailWord_8187379, baseEnd_8187379] using wordTrace_append hprefix tailTrace_8187379
  have hstable : (prefixWord ++ tailWord_8187379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187379).length < 2 ^ (prefixWord ++ tailWord_8187379).sum := by decide
  have hdescent : baseEnd_8187379 < baseStart_8187379 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187383 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 4, 2, 2]
def baseStart_8187383 : Nat := 118140960795 + 8187383 * 2 ^ 59
def prefixEnd_8187383 : Nat := 4983230072969 + 3 ^ 40 * 8187383 * 2
def baseEnd_8187383 : Nat := 4204062781450245560059417

theorem tailTrace_8187383 : CollatzResearch.WordTrace tailWord_8187383 prefixEnd_8187383 4204062781450245560059417 := by
  unfold tailWord_8187383
  simp only [CollatzResearch.WordTrace]
  refine ⟨298618390497517159537662803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199078926998344773025108535 298618390497517159537662803)
  ·
    refine ⟨447927585746275739306494205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298618390497517159537662803 447927585746275739306494205)
    ·
      refine ⟨167972844654853402239935327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447927585746275739306494205 167972844654853402239935327)
      ·
        refine ⟨251959266982280103359902991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167972844654853402239935327 251959266982280103359902991)
        ·
          refine ⟨377938900473420155039854487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251959266982280103359902991 377938900473420155039854487)
          ·
            refine ⟨566908350710130232559781731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377938900473420155039854487 566908350710130232559781731)
            ·
              refine ⟨850362526065195348839672597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566908350710130232559781731 850362526065195348839672597)
              ·
                refine ⟨39860743409306031976859653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 850362526065195348839672597 39860743409306031976859653)
                ·
                  refine ⟨7473889389244880995661185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39860743409306031976859653 7473889389244880995661185)
                  ·
                    refine ⟨5605417041933660746745889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7473889389244880995661185 5605417041933660746745889)
                    ·
                      refine ⟨4204062781450245560059417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5605417041933660746745889 4204062781450245560059417)
                      ·
                        rfl

theorem cell23_8187383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 4, 2, 2].length) (baseStart_8187383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187383 prefixEnd_8187383 := by exact prefixLift 8187383
  have htrace : WordTrace (prefixWord ++ tailWord_8187383) baseStart_8187383 baseEnd_8187383 := by
    simpa [prefixWord, tailWord_8187383, baseEnd_8187383] using wordTrace_append hprefix tailTrace_8187383
  have hstable : (prefixWord ++ tailWord_8187383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187383).length < 2 ^ (prefixWord ++ tailWord_8187383).sum := by decide
  have hdescent : baseEnd_8187383 < baseStart_8187383 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187400 : List Nat := [2, 1, 3, 2, 1, 1, 3, 4, 2, 2, 2]
def baseStart_8187400 : Nat := 118140960795 + 8187400 * 2 ^ 59
def prefixEnd_8187400 : Nat := 4983230072969 + 3 ^ 40 * 8187400 * 2
def baseEnd_8187400 : Nat := 4204071510621371993546839

theorem tailTrace_8187400 : CollatzResearch.WordTrace tailWord_8187400 prefixEnd_8187400 4204071510621371993546839 := by
  unfold tailWord_8187400
  simp only [CollatzResearch.WordTrace]
  refine ⟨149309505269227785720515827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199079340358970380960687769 149309505269227785720515827)
  ·
    refine ⟨223964257903841678580773741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149309505269227785720515827 223964257903841678580773741)
    ·
      refine ⟨83986596713940629467790153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223964257903841678580773741 83986596713940629467790153)
      ·
        refine ⟨62989947535455472100842615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83986596713940629467790153 62989947535455472100842615)
        ·
          refine ⟨94484921303183208151263923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62989947535455472100842615 94484921303183208151263923)
          ·
            refine ⟨141727381954774812226895885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94484921303183208151263923 141727381954774812226895885)
            ·
              refine ⟨53147768233040554585085957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141727381954774812226895885 53147768233040554585085957)
              ·
                refine ⟨9965206543695103984703617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53147768233040554585085957 9965206543695103984703617)
                ·
                  refine ⟨7473904907771327988527713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9965206543695103984703617 7473904907771327988527713)
                  ·
                    refine ⟨5605428680828495991395785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7473904907771327988527713 5605428680828495991395785)
                    ·
                      refine ⟨4204071510621371993546839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5605428680828495991395785 4204071510621371993546839)
                      ·
                        rfl

theorem cell23_8187400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_8187400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187400 prefixEnd_8187400 := by exact prefixLift 8187400
  have htrace : WordTrace (prefixWord ++ tailWord_8187400) baseStart_8187400 baseEnd_8187400 := by
    simpa [prefixWord, tailWord_8187400, baseEnd_8187400] using wordTrace_append hprefix tailTrace_8187400
  have hstable : (prefixWord ++ tailWord_8187400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187400).length < 2 ^ (prefixWord ++ tailWord_8187400).sum := by decide
  have hdescent : baseEnd_8187400 < baseStart_8187400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187456 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 4]
def baseStart_8187456 : Nat := 118140960795 + 8187456 * 2 ^ 59
def prefixEnd_8187456 : Nat := 4983230072969 + 3 ^ 40 * 8187456 * 2
def baseEnd_8187456 : Nat := 4204100265538023774446581

theorem tailTrace_8187456 : CollatzResearch.WordTrace tailWord_8187456 prefixEnd_8187456 4204100265538023774446581 := by
  unfold tailWord_8187456
  simp only [CollatzResearch.WordTrace]
  refine ⟨149310526513126346502535111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199080702017501795336713481 149310526513126346502535111)
  ·
    refine ⟨223965789769689519753802667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149310526513126346502535111 223965789769689519753802667)
    ·
      refine ⟨335948684654534279630704001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223965789769689519753802667 335948684654534279630704001)
      ·
        refine ⟨251961513490900709723028001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335948684654534279630704001 251961513490900709723028001)
        ·
          refine ⟨188971135118175532292271001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251961513490900709723028001 188971135118175532292271001)
          ·
            refine ⟨141728351338631649219203251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188971135118175532292271001 141728351338631649219203251)
            ·
              refine ⟨212592527007947473828804877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141728351338631649219203251 212592527007947473828804877)
              ·
                refine ⟨79722197627980302685801829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212592527007947473828804877 79722197627980302685801829)
                ·
                  refine ⟨14947912055246306753587843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79722197627980302685801829 14947912055246306753587843)
                  ·
                    refine ⟨22421868082869460130381765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14947912055246306753587843 22421868082869460130381765)
                    ·
                      refine ⟨4204100265538023774446581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22421868082869460130381765 4204100265538023774446581)
                      ·
                        rfl

theorem cell23_8187456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_8187456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187456 prefixEnd_8187456 := by exact prefixLift 8187456
  have htrace : WordTrace (prefixWord ++ tailWord_8187456) baseStart_8187456 baseEnd_8187456 := by
    simpa [prefixWord, tailWord_8187456, baseEnd_8187456] using wordTrace_append hprefix tailTrace_8187456
  have hstable : (prefixWord ++ tailWord_8187456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187456).length < 2 ^ (prefixWord ++ tailWord_8187456).sum := by decide
  have hdescent : baseEnd_8187456 < baseStart_8187456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187473 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 2, 4, 2]
def baseStart_8187473 : Nat := 118140960795 + 8187473 * 2 ^ 59
def prefixEnd_8187473 : Nat := 4983230072969 + 3 ^ 40 * 8187473 * 2
def baseEnd_8187473 : Nat := 4204108994709150207934003

theorem tailTrace_8187473 : CollatzResearch.WordTrace tailWord_8187473 prefixEnd_8187473 4204108994709150207934003 := by
  unfold tailWord_8187473
  simp only [CollatzResearch.WordTrace]
  refine ⟨298621673067191104908439073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199081115378127403272292715 298621673067191104908439073)
  ·
    refine ⟨223966254800393328681329305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298621673067191104908439073 223966254800393328681329305)
    ·
      refine ⟨167974691100294996510996979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223966254800393328681329305 167974691100294996510996979)
      ·
        refine ⟨251962036650442494766495469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167974691100294996510996979 251962036650442494766495469)
        ·
          refine ⟨94485763743915935537435801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251962036650442494766495469 94485763743915935537435801)
          ·
            refine ⟨70864322807936951653076851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94485763743915935537435801 70864322807936951653076851)
            ·
              refine ⟨106296484211905427479615277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70864322807936951653076851 106296484211905427479615277)
              ·
                refine ⟨39861181579464535304855729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106296484211905427479615277 39861181579464535304855729)
                ·
                  refine ⟨29895886184598401478641797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39861181579464535304855729 29895886184598401478641797)
                  ·
                    refine ⟨5605478659612200277245337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29895886184598401478641797 5605478659612200277245337)
                    ·
                      refine ⟨4204108994709150207934003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5605478659612200277245337 4204108994709150207934003)
                      ·
                        rfl

theorem cell23_8187473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 4, 2].length) (baseStart_8187473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187473 prefixEnd_8187473 := by exact prefixLift 8187473
  have htrace : WordTrace (prefixWord ++ tailWord_8187473) baseStart_8187473 baseEnd_8187473 := by
    simpa [prefixWord, tailWord_8187473, baseEnd_8187473] using wordTrace_append hprefix tailTrace_8187473
  have hstable : (prefixWord ++ tailWord_8187473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187473).length < 2 ^ (prefixWord ++ tailWord_8187473).sum := by decide
  have hdescent : baseEnd_8187473 < baseStart_8187473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187493 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 1, 4, 3]
def baseStart_8187493 : Nat := 118140960795 + 8187493 * 2 ^ 59
def prefixEnd_8187493 : Nat := 4983230072969 + 3 ^ 40 * 8187493 * 2
def baseEnd_8187493 : Nat := 4204119264322240129683911

theorem tailTrace_8187493 : CollatzResearch.WordTrace tailWord_8187493 prefixEnd_8187493 4204119264322240129683911 := by
  unfold tailWord_8187493
  simp only [CollatzResearch.WordTrace]
  refine ⟨298622402527118648324167133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199081601684745765549444755 298622402527118648324167133)
  ·
    refine ⟨111983400947669493121562675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298622402527118648324167133 111983400947669493121562675)
    ·
      refine ⟨167975101421504239682344013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111983400947669493121562675 167975101421504239682344013)
      ·
        refine ⟨62990663033064089880879005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167975101421504239682344013 62990663033064089880879005)
        ·
          refine ⟨23621498637399033705329627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62990663033064089880879005 23621498637399033705329627)
          ·
            refine ⟨35432247956098550557994441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23621498637399033705329627 35432247956098550557994441)
            ·
              refine ⟨26574185967073912918495831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35432247956098550557994441 26574185967073912918495831)
              ·
                refine ⟨39861278950610869377743747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26574185967073912918495831 39861278950610869377743747)
                ·
                  refine ⟨59791918425916304066615621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39861278950610869377743747 59791918425916304066615621)
                  ·
                    refine ⟨11210984704859307012490429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59791918425916304066615621 11210984704859307012490429)
                    ·
                      refine ⟨4204119264322240129683911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11210984704859307012490429 4204119264322240129683911)
                      ·
                        rfl

theorem cell23_8187493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_8187493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187493 prefixEnd_8187493 := by exact prefixLift 8187493
  have htrace : WordTrace (prefixWord ++ tailWord_8187493) baseStart_8187493 baseEnd_8187493 := by
    simpa [prefixWord, tailWord_8187493, baseEnd_8187493] using wordTrace_append hprefix tailTrace_8187493
  have hstable : (prefixWord ++ tailWord_8187493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187493).length < 2 ^ (prefixWord ++ tailWord_8187493).sum := by decide
  have hdescent : baseEnd_8187493 < baseStart_8187493 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187510 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_8187510 : Nat := 118140960795 + 8187510 * 2 ^ 59
def prefixEnd_8187510 : Nat := 4983230072969 + 3 ^ 40 * 8187510 * 2
def baseEnd_8187510 : Nat := 4204127993493366563171333

theorem tailTrace_8187510 : CollatzResearch.WordTrace tailWord_8187510 prefixEnd_8187510 4204127993493366563171333 := by
  unfold tailWord_8187510
  simp only [CollatzResearch.WordTrace]
  refine ⟨18663938910503566264220999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199082015045371373485023989 18663938910503566264220999)
  ·
    refine ⟨27995908365755349396331499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18663938910503566264220999 27995908365755349396331499)
    ·
      refine ⟨41993862548633024094497249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27995908365755349396331499 41993862548633024094497249)
      ·
        refine ⟨31495396911474768070872937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41993862548633024094497249 31495396911474768070872937)
        ·
          refine ⟨23621547683606076053154703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31495396911474768070872937 23621547683606076053154703)
          ·
            refine ⟨35432321525409114079732055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23621547683606076053154703 35432321525409114079732055)
            ·
              refine ⟨53148482288113671119598083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35432321525409114079732055 53148482288113671119598083)
              ·
                refine ⟨79722723432170506679397125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53148482288113671119598083 79722723432170506679397125)
                ·
                  refine ⟨14948010643531970002386961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79722723432170506679397125 14948010643531970002386961)
                  ·
                    refine ⟨11211007982648977501790221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14948010643531970002386961 11211007982648977501790221)
                    ·
                      refine ⟨4204127993493366563171333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11211007982648977501790221 4204127993493366563171333)
                      ·
                        rfl

theorem cell23_8187510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_8187510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187510 prefixEnd_8187510 := by exact prefixLift 8187510
  have htrace : WordTrace (prefixWord ++ tailWord_8187510) baseStart_8187510 baseEnd_8187510 := by
    simpa [prefixWord, tailWord_8187510, baseEnd_8187510] using wordTrace_append hprefix tailTrace_8187510
  have hstable : (prefixWord ++ tailWord_8187510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187510).length < 2 ^ (prefixWord ++ tailWord_8187510).sum := by decide
  have hdescent : baseEnd_8187510 < baseStart_8187510 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187530 : List Nat := [3, 1, 2, 3, 2, 1, 4, 1, 6]
def baseStart_8187530 : Nat := 118140960795 + 8187530 * 2 ^ 59
def prefixEnd_8187530 : Nat := 4983230072969 + 3 ^ 40 * 8187530 * 2
def baseEnd_8187530 : Nat := 467126473678495164991249

theorem tailTrace_8187530 : CollatzResearch.WordTrace tailWord_8187530 prefixEnd_8187530 467126473678495164991249 := by
  unfold tailWord_8187530
  simp only [CollatzResearch.WordTrace]
  refine ⟨74655938006996150910816011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199082501351989735762176029 74655938006996150910816011)
  ·
    refine ⟨111983907010494226366224017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74655938006996150910816011 111983907010494226366224017)
    ·
      refine ⟨83987930257870669774668013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111983907010494226366224017 83987930257870669774668013)
      ·
        refine ⟨31495473846701501165500505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83987930257870669774668013 31495473846701501165500505)
        ·
          refine ⟨23621605385026125874125379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31495473846701501165500505 23621605385026125874125379)
          ·
            refine ⟨35432408077539188811188069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23621605385026125874125379 35432408077539188811188069)
            ·
              refine ⟨6643576514538597902097763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35432408077539188811188069 6643576514538597902097763)
              ·
                refine ⟨9965364771807896853146645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6643576514538597902097763 9965364771807896853146645)
                ·
                  refine ⟨467126473678495164991249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9965364771807896853146645 467126473678495164991249)
                  ·
                    rfl

theorem cell23_8187530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 1, 6].length) (baseStart_8187530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187530 prefixEnd_8187530 := by exact prefixLift 8187530
  have htrace : WordTrace (prefixWord ++ tailWord_8187530) baseStart_8187530 baseEnd_8187530 := by
    simpa [prefixWord, tailWord_8187530, baseEnd_8187530] using wordTrace_append hprefix tailTrace_8187530
  have hstable : (prefixWord ++ tailWord_8187530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187530).length < 2 ^ (prefixWord ++ tailWord_8187530).sum := by decide
  have hdescent : baseEnd_8187530 < baseStart_8187530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187543 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 3, 5]
def baseStart_8187543 : Nat := 118140960795 + 8187543 * 2 ^ 59
def prefixEnd_8187543 : Nat := 4983230072969 + 3 ^ 40 * 8187543 * 2
def baseEnd_8187543 : Nat := 1401381646118321644686227

theorem tailTrace_8187543 : CollatzResearch.WordTrace tailWord_8187543 prefixEnd_8187543 1401381646118321644686227 := by
  unfold tailWord_8187543
  simp only [CollatzResearch.WordTrace]
  refine ⟨298624226176937506863487283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199082817451291671242324855 298624226176937506863487283)
  ·
    refine ⟨447936339265406260295230925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298624226176937506863487283 447936339265406260295230925)
    ·
      refine ⟨167976127224527347610711597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447936339265406260295230925 167976127224527347610711597)
      ·
        refine ⟨62991047709197755354016849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167976127224527347610711597 62991047709197755354016849)
        ·
          refine ⟨47243285781898316515512637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62991047709197755354016849 47243285781898316515512637)
          ·
            refine ⟨17716232168211868693317239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47243285781898316515512637 17716232168211868693317239)
            ·
              refine ⟨26574348252317803039975859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17716232168211868693317239 26574348252317803039975859)
              ·
                refine ⟨39861522378476704559963789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26574348252317803039975859 39861522378476704559963789)
                ·
                  refine ⟨14948070891928764209986421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39861522378476704559963789 14948070891928764209986421)
                  ·
                    refine ⟨1401381646118321644686227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14948070891928764209986421 1401381646118321644686227)
                    ·
                      rfl

theorem cell23_8187543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_8187543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187543 prefixEnd_8187543 := by exact prefixLift 8187543
  have htrace : WordTrace (prefixWord ++ tailWord_8187543) baseStart_8187543 baseEnd_8187543 := by
    simpa [prefixWord, tailWord_8187543, baseEnd_8187543] using wordTrace_append hprefix tailTrace_8187543
  have hstable : (prefixWord ++ tailWord_8187543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187543).length < 2 ^ (prefixWord ++ tailWord_8187543).sum := by decide
  have hdescent : baseEnd_8187543 < baseStart_8187543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187576 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_8187576 : Nat := 118140960795 + 8187576 * 2 ^ 59
def prefixEnd_8187576 : Nat := 4983230072969 + 3 ^ 40 * 8187576 * 2
def baseEnd_8187576 : Nat := 4204161883216563304946029

theorem tailTrace_8187576 : CollatzResearch.WordTrace tailWord_8187576 prefixEnd_8187576 4204161883216563304946029 := by
  unfold tailWord_8187576
  simp only [CollatzResearch.WordTrace]
  refine ⟨149312714892908976749719291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199083619857211968999625721 149312714892908976749719291)
  ·
    refine ⟨223969072339363465124578937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149312714892908976749719291 223969072339363465124578937)
    ·
      refine ⟨167976804254522598843434203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223969072339363465124578937 167976804254522598843434203)
      ·
        refine ⟨251965206381783898265151305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167976804254522598843434203 251965206381783898265151305)
        ·
          refine ⟨188973904786337923698863479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251965206381783898265151305 188973904786337923698863479)
          ·
            refine ⟨283460857179506885548295219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188973904786337923698863479 283460857179506885548295219)
            ·
              refine ⟨425191285769260328322442829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283460857179506885548295219 425191285769260328322442829)
              ·
                refine ⟨159446732163472623120916061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 425191285769260328322442829 159446732163472623120916061)
                ·
                  refine ⟨59792524561302233670343523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159446732163472623120916061 59792524561302233670343523)
                  ·
                    refine ⟨89688786841953350505515285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59792524561302233670343523 89688786841953350505515285)
                    ·
                      refine ⟨4204161883216563304946029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89688786841953350505515285 4204161883216563304946029)
                      ·
                        rfl

theorem cell23_8187576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_8187576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187576 prefixEnd_8187576 := by exact prefixLift 8187576
  have htrace : WordTrace (prefixWord ++ tailWord_8187576) baseStart_8187576 baseEnd_8187576 := by
    simpa [prefixWord, tailWord_8187576, baseEnd_8187576] using wordTrace_append hprefix tailTrace_8187576
  have hstable : (prefixWord ++ tailWord_8187576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187576).length < 2 ^ (prefixWord ++ tailWord_8187576).sum := by decide
  have hdescent : baseEnd_8187576 < baseStart_8187576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187583 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 3]
def baseStart_8187583 : Nat := 118140960795 + 8187583 * 2 ^ 59
def prefixEnd_8187583 : Nat := 4983230072969 + 3 ^ 40 * 8187583 * 2
def baseEnd_8187583 : Nat := 4204165477581144777558497

theorem tailTrace_8187583 : CollatzResearch.WordTrace tailWord_8187583 prefixEnd_8187583 4204165477581144777558497 := by
  unfold tailWord_8187583
  simp only [CollatzResearch.WordTrace]
  refine ⟨298625685096792593694943403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199083790064528395796628935 298625685096792593694943403)
  ·
    refine ⟨447938527645188890542415105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298625685096792593694943403 447938527645188890542415105)
    ·
      refine ⟨335953895733891667906811329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447938527645188890542415105 335953895733891667906811329)
      ·
        refine ⟨251965421800418750930108497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335953895733891667906811329 251965421800418750930108497)
        ·
          refine ⟨188974066350314063197581373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251965421800418750930108497 188974066350314063197581373)
          ·
            refine ⟨70865274881367773699093015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188974066350314063197581373 70865274881367773699093015)
            ·
              refine ⟨106297912322051660548639523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70865274881367773699093015 106297912322051660548639523)
              ·
                refine ⟨159446868483077490822959285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106297912322051660548639523 159446868483077490822959285)
                ·
                  refine ⟨14948143920288514764652433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159446868483077490822959285 14948143920288514764652433)
                  ·
                    refine ⟨11211107940216386073489325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14948143920288514764652433 11211107940216386073489325)
                    ·
                      refine ⟨4204165477581144777558497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11211107940216386073489325 4204165477581144777558497)
                      ·
                        rfl

theorem cell23_8187583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 3].length) (baseStart_8187583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187583 prefixEnd_8187583 := by exact prefixLift 8187583
  have htrace : WordTrace (prefixWord ++ tailWord_8187583) baseStart_8187583 baseEnd_8187583 := by
    simpa [prefixWord, tailWord_8187583, baseEnd_8187583] using wordTrace_append hprefix tailTrace_8187583
  have hstable : (prefixWord ++ tailWord_8187583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187583).length < 2 ^ (prefixWord ++ tailWord_8187583).sum := by decide
  have hdescent : baseEnd_8187583 < baseStart_8187583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187597 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_8187597 : Nat := 118140960795 + 8187597 * 2 ^ 59
def prefixEnd_8187597 : Nat := 4983230072969 + 3 ^ 40 * 8187597 * 2
def baseEnd_8187597 : Nat := 4204172666310307722783433

theorem tailTrace_8187597 : CollatzResearch.WordTrace tailWord_8187597 prefixEnd_8187597 4204172666310307722783433 := by
  unfold tailWord_8187597
  simp only [CollatzResearch.WordTrace]
  refine ⟨298626195718741874085953045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199084130479161249390635363 298626195718741874085953045)
  ·
    refine ⟨13998102924316025347779049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 298626195718741874085953045 13998102924316025347779049)
    ·
      refine ⟨10498577193237019010834287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13998102924316025347779049 10498577193237019010834287)
      ·
        refine ⟨15747865789855528516251431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10498577193237019010834287 15747865789855528516251431)
        ·
          refine ⟨23621798684783292774377147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15747865789855528516251431 23621798684783292774377147)
          ·
            refine ⟨35432698027174939161565721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23621798684783292774377147 35432698027174939161565721)
            ·
              refine ⟨26574523520381204371174291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35432698027174939161565721 26574523520381204371174291)
              ·
                refine ⟨39861785280571806556761437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26574523520381204371174291 39861785280571806556761437)
                ·
                  refine ⟨14948169480214427458785539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39861785280571806556761437 14948169480214427458785539)
                  ·
                    refine ⟨22422254220321641188178309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14948169480214427458785539 22422254220321641188178309)
                    ·
                      refine ⟨4204172666310307722783433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22422254220321641188178309 4204172666310307722783433)
                      ·
                        rfl

theorem cell23_8187597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_8187597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187597 prefixEnd_8187597 := by exact prefixLift 8187597
  have htrace : WordTrace (prefixWord ++ tailWord_8187597) baseStart_8187597 baseEnd_8187597 := by
    simpa [prefixWord, tailWord_8187597, baseEnd_8187597] using wordTrace_append hprefix tailTrace_8187597
  have hstable : (prefixWord ++ tailWord_8187597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187597).length < 2 ^ (prefixWord ++ tailWord_8187597).sum := by decide
  have hdescent : baseEnd_8187597 < baseStart_8187597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187617 : List Nat := [1, 2, 3, 1, 5, 1, 1, 3, 1, 2, 3]
def baseStart_8187617 : Nat := 118140960795 + 8187617 * 2 ^ 59
def prefixEnd_8187617 : Nat := 4983230072969 + 3 ^ 40 * 8187617 * 2
def baseEnd_8187617 : Nat := 4204182935923397644533341

theorem tailTrace_8187617 : CollatzResearch.WordTrace tailWord_8187617 prefixEnd_8187617 4204182935923397644533341 := by
  unfold tailWord_8187617
  simp only [CollatzResearch.WordTrace]
  refine ⟨298626925178669417501681105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199084616785779611667787403 298626925178669417501681105)
  ·
    refine ⟨223970193884002063126260829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298626925178669417501681105 223970193884002063126260829)
    ·
      refine ⟨83988822706500773672347811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223970193884002063126260829 83988822706500773672347811)
      ·
        refine ⟨125983234059751160508521717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83988822706500773672347811 125983234059751160508521717)
        ·
          refine ⟨11810928193101671297673911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125983234059751160508521717 11810928193101671297673911)
          ·
            refine ⟨17716392289652506946510867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11810928193101671297673911 17716392289652506946510867)
            ·
              refine ⟨26574588434478760419766301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17716392289652506946510867 26574588434478760419766301)
              ·
                refine ⟨9965470662929535157412363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26574588434478760419766301 9965470662929535157412363)
                ·
                  refine ⟨14948205994394302736118545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9965470662929535157412363 14948205994394302736118545)
                  ·
                    refine ⟨11211154495795727052088909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14948205994394302736118545 11211154495795727052088909)
                    ·
                      refine ⟨4204182935923397644533341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11211154495795727052088909 4204182935923397644533341)
                      ·
                        rfl

theorem cell23_8187617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_8187617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187617 prefixEnd_8187617 := by exact prefixLift 8187617
  have htrace : WordTrace (prefixWord ++ tailWord_8187617) baseStart_8187617 baseEnd_8187617 := by
    simpa [prefixWord, tailWord_8187617, baseEnd_8187617] using wordTrace_append hprefix tailTrace_8187617
  have hstable : (prefixWord ++ tailWord_8187617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187617).length < 2 ^ (prefixWord ++ tailWord_8187617).sum := by decide
  have hdescent : baseEnd_8187617 < baseStart_8187617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187640 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 3, 3, 2]
def baseStart_8187640 : Nat := 118140960795 + 8187640 * 2 ^ 59
def prefixEnd_8187640 : Nat := 4983230072969 + 3 ^ 40 * 8187640 * 2
def baseEnd_8187640 : Nat := 4204194745978451054545735

theorem tailTrace_8187640 : CollatzResearch.WordTrace tailWord_8187640 prefixEnd_8187640 4204194745978451054545735 := by
  unfold tailWord_8187640
  simp only [CollatzResearch.WordTrace]
  refine ⟨149313882028793046214884187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199085176038390728286512249 149313882028793046214884187)
  ·
    refine ⟨223970823043189569322326281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149313882028793046214884187 223970823043189569322326281)
    ·
      refine ⟨167978117282392176991744711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223970823043189569322326281 167978117282392176991744711)
      ·
        refine ⟨251967175923588265487617067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167978117282392176991744711 251967175923588265487617067)
        ·
          refine ⟨377950763885382398231425601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251967175923588265487617067 377950763885382398231425601)
          ·
            refine ⟨283463072914036798673569201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377950763885382398231425601 283463072914036798673569201)
            ·
              refine ⟨212597304685527599005176901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283463072914036798673569201 212597304685527599005176901)
              ·
                refine ⟨39861994628536424813470669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212597304685527599005176901 39861994628536424813470669)
                ·
                  refine ⟨14948247985701159305051501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39861994628536424813470669 14948247985701159305051501)
                  ·
                    refine ⟨5605592994637934739394313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14948247985701159305051501 5605592994637934739394313)
                    ·
                      refine ⟨4204194745978451054545735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5605592994637934739394313 4204194745978451054545735)
                      ·
                        rfl

theorem cell23_8187640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3, 3, 2].length) (baseStart_8187640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187640 prefixEnd_8187640 := by exact prefixLift 8187640
  have htrace : WordTrace (prefixWord ++ tailWord_8187640) baseStart_8187640 baseEnd_8187640 := by
    simpa [prefixWord, tailWord_8187640, baseEnd_8187640] using wordTrace_append hprefix tailTrace_8187640
  have hstable : (prefixWord ++ tailWord_8187640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187640).length < 2 ^ (prefixWord ++ tailWord_8187640).sum := by decide
  have hdescent : baseEnd_8187640 < baseStart_8187640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187683 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 4]
def baseStart_8187683 : Nat := 118140960795 + 8187683 * 2 ^ 59
def prefixEnd_8187683 : Nat := 4983230072969 + 3 ^ 40 * 8187683 * 2
def baseEnd_8187683 : Nat := 4204216825646594386308037

theorem tailTrace_8187683 : CollatzResearch.WordTrace tailWord_8187683 prefixEnd_8187683 4204216825646594386308037 := by
  unfold tailWord_8187683
  simp only [CollatzResearch.WordTrace]
  refine ⟨298629332396430310773583703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199086221597620207182389135 298629332396430310773583703)
  ·
    refine ⟨447943998594645466160375555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298629332396430310773583703 447943998594645466160375555)
    ·
      refine ⟨671915997891968199240563333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447943998594645466160375555 671915997891968199240563333)
      ·
        refine ⟨125984249604744037357605625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 671915997891968199240563333 125984249604744037357605625)
        ·
          refine ⟨94488187203558028018204219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125984249604744037357605625 94488187203558028018204219)
          ·
            refine ⟨141732280805337042027306329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94488187203558028018204219 141732280805337042027306329)
            ·
              refine ⟨106299210604002781520479747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141732280805337042027306329 106299210604002781520479747)
              ·
                refine ⟨159448815906004172280719621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106299210604002781520479747 159448815906004172280719621)
                ·
                  refine ⟨29896652982375782302634929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159448815906004172280719621 29896652982375782302634929)
                  ·
                    refine ⟨22422489736781836726976197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29896652982375782302634929 22422489736781836726976197)
                    ·
                      refine ⟨4204216825646594386308037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22422489736781836726976197 4204216825646594386308037)
                      ·
                        rfl

theorem cell23_8187683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_8187683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187683 prefixEnd_8187683 := by exact prefixLift 8187683
  have htrace : WordTrace (prefixWord ++ tailWord_8187683) baseStart_8187683 baseEnd_8187683 := by
    simpa [prefixWord, tailWord_8187683, baseEnd_8187683] using wordTrace_append hprefix tailTrace_8187683
  have hstable : (prefixWord ++ tailWord_8187683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187683).length < 2 ^ (prefixWord ++ tailWord_8187683).sum := by decide
  have hdescent : baseEnd_8187683 < baseStart_8187683 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187704 : List Nat := [2, 1, 2, 1, 3, 4, 1, 3, 2, 2, 2]
def baseStart_8187704 : Nat := 118140960795 + 8187704 * 2 ^ 59
def prefixEnd_8187704 : Nat := 4983230072969 + 3 ^ 40 * 8187704 * 2
def baseEnd_8187704 : Nat := 4204227608740338804145441

theorem tailTrace_8187704 : CollatzResearch.WordTrace tailWord_8187704 prefixEnd_8187704 4204227608740338804145441 := by
  unfold tailWord_8187704
  simp only [CollatzResearch.WordTrace]
  refine ⟨149315049164677115680049083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199086732219569487573398777 149315049164677115680049083)
  ·
    refine ⟨223972573747015673520073625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149315049164677115680049083 223972573747015673520073625)
    ·
      refine ⟨167979430310261755140055219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223972573747015673520073625 167979430310261755140055219)
      ·
        refine ⟨251969145465392632710082829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167979430310261755140055219 251969145465392632710082829)
        ·
          refine ⟨94488429549522237266281061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251969145465392632710082829 94488429549522237266281061)
          ·
            refine ⟨17716580540535419487427699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94488429549522237266281061 17716580540535419487427699)
            ·
              refine ⟨26574870810803129231141549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17716580540535419487427699 26574870810803129231141549)
              ·
                refine ⟨9965576554051173461678081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26574870810803129231141549 9965576554051173461678081)
                ·
                  refine ⟨7474182415538380096258561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9965576554051173461678081 7474182415538380096258561)
                  ·
                    refine ⟨5605636811653785072193921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7474182415538380096258561 5605636811653785072193921)
                    ·
                      refine ⟨4204227608740338804145441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5605636811653785072193921 4204227608740338804145441)
                      ·
                        rfl

theorem cell23_8187704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 3, 2, 2, 2].length) (baseStart_8187704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187704 prefixEnd_8187704 := by exact prefixLift 8187704
  have htrace : WordTrace (prefixWord ++ tailWord_8187704) baseStart_8187704 baseEnd_8187704 := by
    simpa [prefixWord, tailWord_8187704, baseEnd_8187704] using wordTrace_append hprefix tailTrace_8187704
  have hstable : (prefixWord ++ tailWord_8187704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187704).length < 2 ^ (prefixWord ++ tailWord_8187704).sum := by decide
  have hdescent : baseEnd_8187704 < baseStart_8187704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187744 : List Nat := [2, 1, 1, 3, 3, 4, 2, 2, 5]
def baseStart_8187744 : Nat := 118140960795 + 8187744 * 2 ^ 59
def prefixEnd_8187744 : Nat := 4983230072969 + 3 ^ 40 * 8187744 * 2
def baseEnd_8187744 : Nat := 467138683107390960849473

theorem tailTrace_8187744 : CollatzResearch.WordTrace tailWord_8187744 prefixEnd_8187744 467138683107390960849473 := by
  unfold tailWord_8187744
  simp only [CollatzResearch.WordTrace]
  refine ⟨149315778624604659095777143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199087704832806212127702857 149315778624604659095777143)
  ·
    refine ⟨223973667936906988643665715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149315778624604659095777143 223973667936906988643665715)
    ·
      refine ⟨335960501905360482965498573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223973667936906988643665715 335960501905360482965498573)
      ·
        refine ⟨125985188214510181112061965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335960501905360482965498573 125985188214510181112061965)
        ·
          refine ⟨47244445580441317917023237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125985188214510181112061965 47244445580441317917023237)
          ·
            refine ⟨8858333546332747109441857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47244445580441317917023237 8858333546332747109441857)
            ·
              refine ⟨6643750159749560332081393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8858333546332747109441857 6643750159749560332081393)
              ·
                refine ⟨4982812619812170249061045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6643750159749560332081393 4982812619812170249061045)
                ·
                  refine ⟨467138683107390960849473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4982812619812170249061045 467138683107390960849473)
                  ·
                    rfl

theorem cell23_8187744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 5].length) (baseStart_8187744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187744 prefixEnd_8187744 := by exact prefixLift 8187744
  have htrace : WordTrace (prefixWord ++ tailWord_8187744) baseStart_8187744 baseEnd_8187744 := by
    simpa [prefixWord, tailWord_8187744, baseEnd_8187744] using wordTrace_append hprefix tailTrace_8187744
  have hstable : (prefixWord ++ tailWord_8187744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187744).length < 2 ^ (prefixWord ++ tailWord_8187744).sum := by decide
  have hdescent : baseEnd_8187744 < baseStart_8187744 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187754 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_8187754 : Nat := 118140960795 + 8187754 * 2 ^ 59
def prefixEnd_8187754 : Nat := 4983230072969 + 3 ^ 40 * 8187754 * 2
def baseEnd_8187754 : Nat := 4204253282773063608520211

theorem tailTrace_8187754 : CollatzResearch.WordTrace tailWord_8187754 prefixEnd_8187754 4204253282773063608520211 := by
  unfold tailWord_8187754
  simp only [CollatzResearch.WordTrace]
  refine ⟨74657980494793272474854579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199087947986115393266278877 74657980494793272474854579)
  ·
    refine ⟨111986970742189908712281869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74657980494793272474854579 111986970742189908712281869)
    ·
      refine ⟨41995114028321215767105701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111986970742189908712281869 41995114028321215767105701)
      ·
        refine ⟨7874083880310227956332319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41995114028321215767105701 7874083880310227956332319)
        ·
          refine ⟨11811125820465341934498479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7874083880310227956332319 11811125820465341934498479)
          ·
            refine ⟨17716688730698012901747719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11811125820465341934498479 17716688730698012901747719)
            ·
              refine ⟨26575033096047019352621579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17716688730698012901747719 26575033096047019352621579)
              ·
                refine ⟨39862549644070529028932369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26575033096047019352621579 39862549644070529028932369)
                ·
                  refine ⟨29896912233052896771699277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39862549644070529028932369 29896912233052896771699277)
                  ·
                    refine ⟨11211342087394836289387229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29896912233052896771699277 11211342087394836289387229)
                    ·
                      refine ⟨4204253282773063608520211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11211342087394836289387229 4204253282773063608520211)
                      ·
                        rfl

theorem cell23_8187754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_8187754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187754 prefixEnd_8187754 := by exact prefixLift 8187754
  have htrace : WordTrace (prefixWord ++ tailWord_8187754) baseStart_8187754 baseEnd_8187754 := by
    simpa [prefixWord, tailWord_8187754, baseEnd_8187754] using wordTrace_append hprefix tailTrace_8187754
  have hstable : (prefixWord ++ tailWord_8187754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187754).length < 2 ^ (prefixWord ++ tailWord_8187754).sum := by decide
  have hdescent : baseEnd_8187754 < baseStart_8187754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187770 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 5, 4]
def baseStart_8187770 : Nat := 118140960795 + 8187770 * 2 ^ 59
def prefixEnd_8187770 : Nat := 4983230072969 + 3 ^ 40 * 8187770 * 2
def baseEnd_8187770 : Nat := 1401420499487845181973379

theorem tailTrace_8187770 : CollatzResearch.WordTrace tailWord_8187770 prefixEnd_8187770 1401420499487845181973379 := by
  unfold tailWord_8187770
  simp only [CollatzResearch.WordTrace]
  refine ⟨74658126386778781158000191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199088337031410083088000509 74658126386778781158000191)
  ·
    refine ⟨111987189580168171737000287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74658126386778781158000191 111987189580168171737000287)
    ·
      refine ⟨167980784370252257605500431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111987189580168171737000287 167980784370252257605500431)
      ·
        refine ⟨251971176555378386408250647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167980784370252257605500431 251971176555378386408250647)
        ·
          refine ⟨377956764833067579612375971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251971176555378386408250647 377956764833067579612375971)
          ·
            refine ⟨566935147249601369418563957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377956764833067579612375971 566935147249601369418563957)
            ·
              refine ⟨53150170054650128382990371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 566935147249601369418563957 53150170054650128382990371)
              ·
                refine ⟨79725255081975192574485557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53150170054650128382990371 79725255081975192574485557)
                ·
                  refine ⟨7474242663935174303858021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79725255081975192574485557 7474242663935174303858021)
                  ·
                    refine ⟨1401420499487845181973379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7474242663935174303858021 1401420499487845181973379)
                    ·
                      rfl

theorem cell23_8187770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_8187770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187770 prefixEnd_8187770 := by exact prefixLift 8187770
  have htrace : WordTrace (prefixWord ++ tailWord_8187770) baseStart_8187770 baseEnd_8187770 := by
    simpa [prefixWord, tailWord_8187770, baseEnd_8187770] using wordTrace_append hprefix tailTrace_8187770
  have hstable : (prefixWord ++ tailWord_8187770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187770).length < 2 ^ (prefixWord ++ tailWord_8187770).sum := by decide
  have hdescent : baseEnd_8187770 < baseStart_8187770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187774 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_8187774 : Nat := 118140960795 + 8187774 * 2 ^ 59
def prefixEnd_8187774 : Nat := 4983230072969 + 3 ^ 40 * 8187774 * 2
def baseEnd_8187774 : Nat := 1401421184128717843423373

theorem tailTrace_8187774 : CollatzResearch.WordTrace tailWord_8187774 prefixEnd_8187774 1401421184128717843423373 := by
  unfold tailWord_8187774
  simp only [CollatzResearch.WordTrace]
  refine ⟨37329081429887579164393297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199088434292733755543430917 37329081429887579164393297)
  ·
    refine ⟨27996811072415684373294973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37329081429887579164393297 27996811072415684373294973)
    ·
      refine ⟨10498804152155881639985615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27996811072415684373294973 10498804152155881639985615)
      ·
        refine ⟨15748206228233822459978423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10498804152155881639985615 15748206228233822459978423)
        ·
          refine ⟨23622309342350733689967635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15748206228233822459978423 23622309342350733689967635)
          ·
            refine ⟨35433464013526100534951453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23622309342350733689967635 35433464013526100534951453)
            ·
              refine ⟨13287549005072287700606795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35433464013526100534951453 13287549005072287700606795)
              ·
                refine ⟨19931323507608431550910193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13287549005072287700606795 19931323507608431550910193)
                ·
                  refine ⟨14948492630706323663182645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19931323507608431550910193 14948492630706323663182645)
                  ·
                    refine ⟨1401421184128717843423373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14948492630706323663182645 1401421184128717843423373)
                    ·
                      rfl

theorem cell23_8187774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_8187774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187774 prefixEnd_8187774 := by exact prefixLift 8187774
  have htrace : WordTrace (prefixWord ++ tailWord_8187774) baseStart_8187774 baseEnd_8187774 := by
    simpa [prefixWord, tailWord_8187774, baseEnd_8187774] using wordTrace_append hprefix tailTrace_8187774
  have hstable : (prefixWord ++ tailWord_8187774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187774).length < 2 ^ (prefixWord ++ tailWord_8187774).sum := by decide
  have hdescent : baseEnd_8187774 < baseStart_8187774 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187794 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_8187794 : Nat := 118140960795 + 8187794 * 2 ^ 59
def prefixEnd_8187794 : Nat := 4983230072969 + 3 ^ 40 * 8187794 * 2
def baseEnd_8187794 : Nat := 4204273821999243452020027

theorem tailTrace_8187794 : CollatzResearch.WordTrace tailWord_8187794 prefixEnd_8187794 4204273821999243452020027 := by
  unfold tailWord_8187794
  simp only [CollatzResearch.WordTrace]
  refine ⟨74658345224757044182718609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199088920599352117820582957 74658345224757044182718609)
  ·
    refine ⟨55993758918567783137038957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74658345224757044182718609 55993758918567783137038957)
    ·
      refine ⟨20997659594462918676389609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55993758918567783137038957 20997659594462918676389609)
      ·
        refine ⟨15748244695847189007292207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20997659594462918676389609 15748244695847189007292207)
        ·
          refine ⟨23622367043770783510938311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15748244695847189007292207 23622367043770783510938311)
          ·
            refine ⟨35433550565656175266407467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23622367043770783510938311 35433550565656175266407467)
            ·
              refine ⟨53150325848484262899611201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35433550565656175266407467 53150325848484262899611201)
              ·
                refine ⟨39862744386363197174708401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53150325848484262899611201 39862744386363197174708401)
                ·
                  refine ⟨29897058289772397881031301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39862744386363197174708401 29897058289772397881031301)
                  ·
                    refine ⟨5605698429332324602693369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29897058289772397881031301 5605698429332324602693369)
                    ·
                      refine ⟨4204273821999243452020027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5605698429332324602693369 4204273821999243452020027)
                      ·
                        rfl

theorem cell23_8187794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_8187794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187794 prefixEnd_8187794 := by exact prefixLift 8187794
  have htrace : WordTrace (prefixWord ++ tailWord_8187794) baseStart_8187794 baseEnd_8187794 := by
    simpa [prefixWord, tailWord_8187794, baseEnd_8187794] using wordTrace_append hprefix tailTrace_8187794
  have hstable : (prefixWord ++ tailWord_8187794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187794).length < 2 ^ (prefixWord ++ tailWord_8187794).sum := by decide
  have hdescent : baseEnd_8187794 < baseStart_8187794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187804 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 3, 4]
def baseStart_8187804 : Nat := 118140960795 + 8187804 * 2 ^ 59
def prefixEnd_8187804 : Nat := 4983230072969 + 3 ^ 40 * 8187804 * 2
def baseEnd_8187804 : Nat := 1401426318935262804298327

theorem tailTrace_8187804 : CollatzResearch.WordTrace tailWord_8187804 prefixEnd_8187804 1401426318935262804298327 := by
  unfold tailWord_8187804
  simp only [CollatzResearch.WordTrace]
  refine ⟨149316872814495974219369233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199089163752661298959158977 149316872814495974219369233)
  ·
    refine ⟨111987654610871980664526925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149316872814495974219369233 111987654610871980664526925)
    ·
      refine ⟨41995370479076992749197597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111987654610871980664526925 41995370479076992749197597)
      ·
        refine ⟨15748263929653872280949099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41995370479076992749197597 15748263929653872280949099)
        ·
          refine ⟨23622395894480808421423649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15748263929653872280949099 23622395894480808421423649)
          ·
            refine ⟨17716796920860606316067737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23622395894480808421423649 17716796920860606316067737)
            ·
              refine ⟨13287597690645454737050803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17716796920860606316067737 13287597690645454737050803)
              ·
                refine ⟨19931396535968182105576205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13287597690645454737050803 19931396535968182105576205)
                ·
                  refine ⟨7474273700988068289591077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19931396535968182105576205 7474273700988068289591077)
                  ·
                    refine ⟨1401426318935262804298327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7474273700988068289591077 1401426318935262804298327)
                    ·
                      rfl

theorem cell23_8187804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_8187804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187804 prefixEnd_8187804 := by exact prefixLift 8187804
  have htrace : WordTrace (prefixWord ++ tailWord_8187804) baseStart_8187804 baseEnd_8187804 := by
    simpa [prefixWord, tailWord_8187804, baseEnd_8187804] using wordTrace_append hprefix tailTrace_8187804
  have hstable : (prefixWord ++ tailWord_8187804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187804).length < 2 ^ (prefixWord ++ tailWord_8187804).sum := by decide
  have hdescent : baseEnd_8187804 < baseStart_8187804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187827 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 3, 1, 3]
def baseStart_8187827 : Nat := 118140960795 + 8187827 * 2 ^ 59
def prefixEnd_8187827 : Nat := 4983230072969 + 3 ^ 40 * 8187827 * 2
def baseEnd_8187827 : Nat := 4204290766860841822907375

theorem tailTrace_8187827 : CollatzResearch.WordTrace tailWord_8187827 prefixEnd_8187827 4204290766860841822907375 := by
  unfold tailWord_8187827
  simp only [CollatzResearch.WordTrace]
  refine ⟨298634584507908623366825735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199089723005272415577883823 298634584507908623366825735)
  ·
    refine ⟨447951876761862935050238603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298634584507908623366825735 447951876761862935050238603)
    ·
      refine ⟨671927815142794402575357905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447951876761862935050238603 671927815142794402575357905)
      ·
        refine ⟨503945861357095801931518429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 671927815142794402575357905 503945861357095801931518429)
        ·
          refine ⟨188979698008910925724319411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503945861357095801931518429 188979698008910925724319411)
          ·
            refine ⟨283469547013366388586479117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188979698008910925724319411 283469547013366388586479117)
            ·
              refine ⟨106301080130012395719929669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283469547013366388586479117 106301080130012395719929669)
              ·
                refine ⟨19931452524377324197486813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106301080130012395719929669 19931452524377324197486813)
                ·
                  refine ⟨7474294696641496574057555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19931452524377324197486813 7474294696641496574057555)
                  ·
                    refine ⟨11211442044962244861086333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7474294696641496574057555 11211442044962244861086333)
                    ·
                      refine ⟨4204290766860841822907375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11211442044962244861086333 4204290766860841822907375)
                      ·
                        rfl

theorem cell23_8187827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 1, 3].length) (baseStart_8187827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187827 prefixEnd_8187827 := by exact prefixLift 8187827
  have htrace : WordTrace (prefixWord ++ tailWord_8187827) baseStart_8187827 baseEnd_8187827 := by
    simpa [prefixWord, tailWord_8187827, baseEnd_8187827] using wordTrace_append hprefix tailTrace_8187827
  have hstable : (prefixWord ++ tailWord_8187827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187827).length < 2 ^ (prefixWord ++ tailWord_8187827).sum := by decide
  have hdescent : baseEnd_8187827 < baseStart_8187827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187854 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2]
def baseStart_8187854 : Nat := 118140960795 + 8187854 * 2 ^ 59
def prefixEnd_8187854 : Nat := 4983230072969 + 3 ^ 40 * 8187854 * 2
def baseEnd_8187854 : Nat := 4204304630838513217269751

theorem tailTrace_8187854 : CollatzResearch.WordTrace tailWord_8187854 prefixEnd_8187854 4204304630838513217269751 := by
  unfold tailWord_8187854
  simp only [CollatzResearch.WordTrace]
  refine ⟨37329446159851350872257327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199090379519207204652039077 37329446159851350872257327)
  ·
    refine ⟨55994169239777026308385991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37329446159851350872257327 55994169239777026308385991)
    ·
      refine ⟨83991253859665539462578987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55994169239777026308385991 83991253859665539462578987)
      ·
        refine ⟨125986880789498309193868481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83991253859665539462578987 125986880789498309193868481)
        ·
          refine ⟨94490160592123731895401361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125986880789498309193868481 94490160592123731895401361)
          ·
            refine ⟨70867620444092798921551021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94490160592123731895401361 70867620444092798921551021)
            ·
              refine ⟨26575357666534799595581633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70867620444092798921551021 26575357666534799595581633)
              ·
                refine ⟨19931518249901099696686225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26575357666534799595581633 19931518249901099696686225)
                ·
                  refine ⟨14948638687425824772514669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19931518249901099696686225 14948638687425824772514669)
                  ·
                    refine ⟨5605739507784684289693001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14948638687425824772514669 5605739507784684289693001)
                    ·
                      refine ⟨4204304630838513217269751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5605739507784684289693001 4204304630838513217269751)
                      ·
                        rfl

theorem cell23_8187854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_8187854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187854 prefixEnd_8187854 := by exact prefixLift 8187854
  have htrace : WordTrace (prefixWord ++ tailWord_8187854) baseStart_8187854 baseEnd_8187854 := by
    simpa [prefixWord, tailWord_8187854, baseEnd_8187854] using wordTrace_append hprefix tailTrace_8187854
  have hstable : (prefixWord ++ tailWord_8187854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187854).length < 2 ^ (prefixWord ++ tailWord_8187854).sum := by decide
  have hdescent : baseEnd_8187854 < baseStart_8187854 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187861 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_8187861 : Nat := 118140960795 + 8187861 * 2 ^ 59
def prefixEnd_8187861 : Nat := 4983230072969 + 3 ^ 40 * 8187861 * 2
def baseEnd_8187861 : Nat := 4204308225203094689882219

theorem tailTrace_8187861 : CollatzResearch.WordTrace tailWord_8187861 prefixEnd_8187861 4204308225203094689882219 := by
  unfold tailWord_8187861
  simp only [CollatzResearch.WordTrace]
  refine ⟨298635824589785447173563437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199090549726523631449042291 298635824589785447173563437)
  ·
    refine ⟨111988434221169542690086289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298635824589785447173563437 111988434221169542690086289)
    ·
      refine ⟨83991325665877157017564717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111988434221169542690086289 83991325665877157017564717)
      ·
        refine ⟨31496747124703933881586769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83991325665877157017564717 31496747124703933881586769)
        ·
          refine ⟨23622560343527950411190077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31496747124703933881586769 23622560343527950411190077)
          ·
            refine ⟨8858460128822981404196279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23622560343527950411190077 8858460128822981404196279)
            ·
              refine ⟨13287690193234472106294419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8858460128822981404196279 13287690193234472106294419)
              ·
                refine ⟨19931535289851708159441629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13287690193234472106294419 19931535289851708159441629)
                ·
                  refine ⟨7474325733694390559790611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19931535289851708159441629 7474325733694390559790611)
                  ·
                    refine ⟨11211488600541585839685917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7474325733694390559790611 11211488600541585839685917)
                    ·
                      refine ⟨4204308225203094689882219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11211488600541585839685917 4204308225203094689882219)
                      ·
                        rfl

theorem cell23_8187861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_8187861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187861 prefixEnd_8187861 := by exact prefixLift 8187861
  have htrace : WordTrace (prefixWord ++ tailWord_8187861) baseStart_8187861 baseEnd_8187861 := by
    simpa [prefixWord, tailWord_8187861, baseEnd_8187861] using wordTrace_append hprefix tailTrace_8187861
  have hstable : (prefixWord ++ tailWord_8187861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187861).length < 2 ^ (prefixWord ++ tailWord_8187861).sum := by decide
  have hdescent : baseEnd_8187861 < baseStart_8187861 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187884 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 3, 2, 2]
def baseStart_8187884 : Nat := 118140960795 + 8187884 * 2 ^ 59
def prefixEnd_8187884 : Nat := 4983230072969 + 3 ^ 40 * 8187884 * 2
def baseEnd_8187884 : Nat := 4204320035258148099894613

theorem tailTrace_8187884 : CollatzResearch.WordTrace tailWord_8187884 prefixEnd_8187884 4204320035258148099894613 := by
  unfold tailWord_8187884
  simp only [CollatzResearch.WordTrace]
  refine ⟨149318331734351061050825353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199091108979134748067767137 149318331734351061050825353)
  ·
    refine ⟨111988748800763295788119015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149318331734351061050825353 111988748800763295788119015)
    ·
      refine ⟨167983123201144943682178523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111988748800763295788119015 167983123201144943682178523)
      ·
        refine ⟨251974684801717415523267785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167983123201144943682178523 251974684801717415523267785)
        ·
          refine ⟨188981013601288061642450839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251974684801717415523267785 188981013601288061642450839)
          ·
            refine ⟨283471520401932092463676259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188981013601288061642450839 283471520401932092463676259)
            ·
              refine ⟨425207280602898138695514389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283471520401932092463676259 425207280602898138695514389)
              ·
                refine ⟨19931591278260850251352237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 425207280602898138695514389 19931591278260850251352237)
                ·
                  refine ⟨7474346729347818844257089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19931591278260850251352237 7474346729347818844257089)
                  ·
                    refine ⟨5605760047010864133192817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7474346729347818844257089 5605760047010864133192817)
                    ·
                      refine ⟨4204320035258148099894613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5605760047010864133192817 4204320035258148099894613)
                      ·
                        rfl

theorem cell23_8187884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 2, 2].length) (baseStart_8187884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187884 prefixEnd_8187884 := by exact prefixLift 8187884
  have htrace : WordTrace (prefixWord ++ tailWord_8187884) baseStart_8187884 baseEnd_8187884 := by
    simpa [prefixWord, tailWord_8187884, baseEnd_8187884] using wordTrace_append hprefix tailTrace_8187884
  have hstable : (prefixWord ++ tailWord_8187884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187884).length < 2 ^ (prefixWord ++ tailWord_8187884).sum := by decide
  have hdescent : baseEnd_8187884 < baseStart_8187884 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187887 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 3]
def baseStart_8187887 : Nat := 118140960795 + 8187887 * 2 ^ 59
def prefixEnd_8187887 : Nat := 4983230072969 + 3 ^ 40 * 8187887 * 2
def baseEnd_8187887 : Nat := 4204321575700111588157099

theorem tailTrace_8187887 : CollatzResearch.WordTrace tailWord_8187887 prefixEnd_8187887 4204321575700111588157099 := by
  unfold tailWord_8187887
  simp only [CollatzResearch.WordTrace]
  refine ⟨298636772887691253614009915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199091181925127502409339943 298636772887691253614009915)
  ·
    refine ⟨447955159331536880421014873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298636772887691253614009915 447955159331536880421014873)
    ·
      refine ⟨335966369498652660315761155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447955159331536880421014873 335966369498652660315761155)
      ·
        refine ⟨503949554247978990473641733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335966369498652660315761155 503949554247978990473641733)
        ·
          refine ⟨94490541421496060713807825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 503949554247978990473641733 94490541421496060713807825)
          ·
            refine ⟨70867906066122045535355869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94490541421496060713807825 70867906066122045535355869)
            ·
              refine ⟨26575464774795767075758451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70867906066122045535355869 26575464774795767075758451)
              ·
                refine ⟨39863197162193650613637677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26575464774795767075758451 39863197162193650613637677)
                ·
                  refine ⟨14948698935822618980114129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39863197162193650613637677 14948698935822618980114129)
                  ·
                    refine ⟨11211524201866964235085597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14948698935822618980114129 11211524201866964235085597)
                    ·
                      refine ⟨4204321575700111588157099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11211524201866964235085597 4204321575700111588157099)
                      ·
                        rfl

theorem cell23_8187887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 3].length) (baseStart_8187887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187887 prefixEnd_8187887 := by exact prefixLift 8187887
  have htrace : WordTrace (prefixWord ++ tailWord_8187887) baseStart_8187887 baseEnd_8187887 := by
    simpa [prefixWord, tailWord_8187887, baseEnd_8187887] using wordTrace_append hprefix tailTrace_8187887
  have hstable : (prefixWord ++ tailWord_8187887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187887).length < 2 ^ (prefixWord ++ tailWord_8187887).sum := by decide
  have hdescent : baseEnd_8187887 < baseStart_8187887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187894 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_8187894 : Nat := 118140960795 + 8187894 * 2 ^ 59
def prefixEnd_8187894 : Nat := 4983230072969 + 3 ^ 40 * 8187894 * 2
def baseEnd_8187894 : Nat := 1401441723354897686923189

theorem tailTrace_8187894 : CollatzResearch.WordTrace tailWord_8187894 prefixEnd_8187894 1401441723354897686923189 := by
  unfold tailWord_8187894
  simp only [CollatzResearch.WordTrace]
  refine ⟨18664814262416618363094671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199091352132443929206343157 18664814262416618363094671)
  ·
    refine ⟨27997221393624927544642007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18664814262416618363094671 27997221393624927544642007)
    ·
      refine ⟨41995832090437391316963011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27997221393624927544642007 41995832090437391316963011)
      ·
        refine ⟨62993748135656086975444517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41995832090437391316963011 62993748135656086975444517)
        ·
          refine ⟨11811327775435516307895847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62993748135656086975444517 11811327775435516307895847)
          ·
            refine ⟨17716991663153274461843771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11811327775435516307895847 17716991663153274461843771)
            ·
              refine ⟨26575487494729911692765657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17716991663153274461843771 26575487494729911692765657)
              ·
                refine ⟨19931615621047433769574243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26575487494729911692765657 19931615621047433769574243)
                ·
                  refine ⟨29897423431571150654361365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19931615621047433769574243 29897423431571150654361365)
                  ·
                    refine ⟨1401441723354897686923189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29897423431571150654361365 1401441723354897686923189)
                    ·
                      rfl

theorem cell23_8187894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_8187894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187894 prefixEnd_8187894 := by exact prefixLift 8187894
  have htrace : WordTrace (prefixWord ++ tailWord_8187894) baseStart_8187894 baseEnd_8187894 := by
    simpa [prefixWord, tailWord_8187894, baseEnd_8187894] using wordTrace_append hprefix tailTrace_8187894
  have hstable : (prefixWord ++ tailWord_8187894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187894).length < 2 ^ (prefixWord ++ tailWord_8187894).sum := by decide
  have hdescent : baseEnd_8187894 < baseStart_8187894 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187897 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 1, 2, 4]
def baseStart_8187897 : Nat := 118140960795 + 8187897 * 2 ^ 59
def prefixEnd_8187897 : Nat := 4983230072969 + 3 ^ 40 * 8187897 * 2
def baseEnd_8187897 : Nat := 4204326710506656549032053

theorem tailTrace_8187897 : CollatzResearch.WordTrace tailWord_8187897 prefixEnd_8187897 4204326710506656549032053 := by
  unfold tailWord_8187897
  simp only [CollatzResearch.WordTrace]
  refine ⟨298637137617655025321873945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199091425078436683547915963 298637137617655025321873945)
  ·
    refine ⟨223977853213241268991405459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298637137617655025321873945 223977853213241268991405459)
    ·
      refine ⟨335966779819861903487108189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223977853213241268991405459 335966779819861903487108189)
      ·
        refine ⟨125987542432448213807665571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335966779819861903487108189 125987542432448213807665571)
        ·
          refine ⟨188981313648672320711498357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125987542432448213807665571 188981313648672320711498357)
          ·
            refine ⟨17716998154563030066702971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188981313648672320711498357 17716998154563030066702971)
            ·
              refine ⟨26575497231844545100054457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17716998154563030066702971 26575497231844545100054457)
              ·
                refine ⟨19931622923883408825040843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26575497231844545100054457 19931622923883408825040843)
                ·
                  refine ⟨29897434385825113237561265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19931622923883408825040843 29897434385825113237561265)
                  ·
                    refine ⟨22423075789368834928170949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29897434385825113237561265 22423075789368834928170949)
                    ·
                      refine ⟨4204326710506656549032053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22423075789368834928170949 4204326710506656549032053)
                      ·
                        rfl

theorem cell23_8187897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_8187897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187897 prefixEnd_8187897 := by exact prefixLift 8187897
  have htrace : WordTrace (prefixWord ++ tailWord_8187897) baseStart_8187897 baseEnd_8187897 := by
    simpa [prefixWord, tailWord_8187897, baseEnd_8187897] using wordTrace_append hprefix tailTrace_8187897
  have hstable : (prefixWord ++ tailWord_8187897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187897).length < 2 ^ (prefixWord ++ tailWord_8187897).sum := by decide
  have hdescent : baseEnd_8187897 < baseStart_8187897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187918 : List Nat := [4, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2]
def baseStart_8187918 : Nat := 118140960795 + 8187918 * 2 ^ 59
def prefixEnd_8187918 : Nat := 4983230072969 + 3 ^ 40 * 8187918 * 2
def baseEnd_8187918 : Nat := 4204337493600400966869457

theorem tailTrace_8187918 : CollatzResearch.WordTrace tailWord_8187918 prefixEnd_8187918 4204337493600400966869457 := by
  unfold tailWord_8187918
  simp only [CollatzResearch.WordTrace]
  refine ⟨37329737943822368238548551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199091935700385963938925605 37329737943822368238548551)
  ·
    refine ⟨55994606915733552357822827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37329737943822368238548551 55994606915733552357822827)
    ·
      refine ⟨83991910373600328536734241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55994606915733552357822827 83991910373600328536734241)
      ·
        refine ⟨62993932780200246402550681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83991910373600328536734241 62993932780200246402550681)
        ·
          refine ⟨47245449585150184801913011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62993932780200246402550681 47245449585150184801913011)
          ·
            refine ⟨70868174377725277202869517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47245449585150184801913011 70868174377725277202869517)
            ·
              refine ⟨26575565391646978951076069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70868174377725277202869517 26575565391646978951076069)
              ·
                refine ⟨4982918510933808553326763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26575565391646978951076069 4982918510933808553326763)
                ·
                  refine ⟨7474377766400712829990145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982918510933808553326763 7474377766400712829990145)
                  ·
                    refine ⟨5605783324800534622492609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7474377766400712829990145 5605783324800534622492609)
                    ·
                      refine ⟨4204337493600400966869457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5605783324800534622492609 4204337493600400966869457)
                      ·
                        rfl

theorem cell23_8187918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_8187918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187918 prefixEnd_8187918 := by exact prefixLift 8187918
  have htrace : WordTrace (prefixWord ++ tailWord_8187918) baseStart_8187918 baseEnd_8187918 := by
    simpa [prefixWord, tailWord_8187918, baseEnd_8187918] using wordTrace_append hprefix tailTrace_8187918
  have hstable : (prefixWord ++ tailWord_8187918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187918).length < 2 ^ (prefixWord ++ tailWord_8187918).sum := by decide
  have hdescent : baseEnd_8187918 < baseStart_8187918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8187991 : List Nat := [1, 1, 3, 2, 2, 1, 2, 5, 2, 2, 2]
def baseStart_8187991 : Nat := 118140960795 + 8187991 * 2 ^ 59
def prefixEnd_8187991 : Nat := 4983230072969 + 3 ^ 40 * 8187991 * 2
def baseEnd_8187991 : Nat := 4204374977688179181256621

theorem tailTrace_8187991 : CollatzResearch.WordTrace tailWord_8187991 prefixEnd_8187991 4204374977688179181256621 := by
  unfold tailWord_8187991
  simp only [CollatzResearch.WordTrace]
  refine ⟨298640566079314479375795827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199093710719542986250530551 298640566079314479375795827)
  ·
    refine ⟨447960849118971719063693741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298640566079314479375795827 447960849118971719063693741)
    ·
      refine ⟨167985318419614394648885153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447960849118971719063693741 167985318419614394648885153)
      ·
        refine ⟨125988988814710795986663865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167985318419614394648885153 125988988814710795986663865)
        ·
          refine ⟨94491741611033096989997899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125988988814710795986663865 94491741611033096989997899)
          ·
            refine ⟨141737612416549645484996849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94491741611033096989997899 141737612416549645484996849)
            ·
              refine ⟨106303209312412234113747637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141737612416549645484996849 106303209312412234113747637)
              ·
                refine ⟨9965925873038646948163841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106303209312412234113747637 9965925873038646948163841)
                ·
                  refine ⟨7474444404778985211122881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9965925873038646948163841 7474444404778985211122881)
                  ·
                    refine ⟨5605833303584238908342161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7474444404778985211122881 5605833303584238908342161)
                    ·
                      refine ⟨4204374977688179181256621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5605833303584238908342161 4204374977688179181256621)
                      ·
                        rfl

theorem cell23_8187991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_8187991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8187991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8187991 prefixEnd_8187991 := by exact prefixLift 8187991
  have htrace : WordTrace (prefixWord ++ tailWord_8187991) baseStart_8187991 baseEnd_8187991 := by
    simpa [prefixWord, tailWord_8187991, baseEnd_8187991] using wordTrace_append hprefix tailTrace_8187991
  have hstable : (prefixWord ++ tailWord_8187991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8187991).length < 2 ^ (prefixWord ++ tailWord_8187991).sum := by decide
  have hdescent : baseEnd_8187991 < baseStart_8187991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8187991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188037 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 7]
def baseStart_8188037 : Nat := 118140960795 + 8188037 * 2 ^ 59
def prefixEnd_8188037 : Nat := 4983230072969 + 3 ^ 40 * 8188037 * 2
def baseEnd_8188037 : Nat := 4204398597798286001281409

theorem tailTrace_8188037 : CollatzResearch.WordTrace tailWord_8188037 prefixEnd_8188037 4204398597798286001281409 := by
  unfold tailWord_8188037
  simp only [CollatzResearch.WordTrace]
  refine ⟨298642243837147829231970365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199094829224765219487980243 298642243837147829231970365)
  ·
    refine ⟨111990841438930435961988887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298642243837147829231970365 111990841438930435961988887)
    ·
      refine ⟨167986262158395653942983331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111990841438930435961988887 167986262158395653942983331)
      ·
        refine ⟨251979393237593480914474997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167986262158395653942983331 251979393237593480914474997)
        ·
          refine ⟨23623068116024388835732031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251979393237593480914474997 23623068116024388835732031)
          ·
            refine ⟨35434602174036583253598047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23623068116024388835732031 35434602174036583253598047)
            ·
              refine ⟨53151903261054874880397071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35434602174036583253598047 53151903261054874880397071)
              ·
                refine ⟨79727854891582312320595607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53151903261054874880397071 79727854891582312320595607)
                ·
                  refine ⟨119591782337373468480893411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79727854891582312320595607 119591782337373468480893411)
                  ·
                    refine ⟨179387673506060202721340117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119591782337373468480893411 179387673506060202721340117)
                    ·
                      refine ⟨4204398597798286001281409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179387673506060202721340117 4204398597798286001281409)
                      ·
                        rfl

theorem cell23_8188037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_8188037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188037 prefixEnd_8188037 := by exact prefixLift 8188037
  have htrace : WordTrace (prefixWord ++ tailWord_8188037) baseStart_8188037 baseEnd_8188037 := by
    simpa [prefixWord, tailWord_8188037, baseEnd_8188037] using wordTrace_append hprefix tailTrace_8188037
  have hstable : (prefixWord ++ tailWord_8188037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188037).length < 2 ^ (prefixWord ++ tailWord_8188037).sum := by decide
  have hdescent : baseEnd_8188037 < baseStart_8188037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188064 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 4]
def baseStart_8188064 : Nat := 118140960795 + 8188064 * 2 ^ 59
def prefixEnd_8188064 : Nat := 4983230072969 + 3 ^ 40 * 8188064 * 2
def baseEnd_8188064 : Nat := 4204412461775957395643785

theorem tailTrace_8188064 : CollatzResearch.WordTrace tailWord_8188064 prefixEnd_8188064 4204412461775957395643785 := by
  unfold tailWord_8188064
  simp only [CollatzResearch.WordTrace]
  refine ⟨149321614304025006421601623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199095485738700008562135497 149321614304025006421601623)
  ·
    refine ⟨223982421456037509632402435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149321614304025006421601623 223982421456037509632402435)
    ·
      refine ⟨335973632184056264448603653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223982421456037509632402435 335973632184056264448603653)
      ·
        refine ⟨62995056034510549584113185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335973632184056264448603653 62995056034510549584113185)
        ·
          refine ⟨47246292025882912188084889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62995056034510549584113185 47246292025882912188084889)
          ·
            refine ⟨35434719019412184141063667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47246292025882912188084889 35434719019412184141063667)
            ·
              refine ⟨53152078529118276211595501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35434719019412184141063667 53152078529118276211595501)
              ·
                refine ⟨19932029448419353579348313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53152078529118276211595501 19932029448419353579348313)
                ·
                  refine ⟨14949022086314515184511235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19932029448419353579348313 14949022086314515184511235)
                  ·
                    refine ⟨22423533129471772776766853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14949022086314515184511235 22423533129471772776766853)
                    ·
                      refine ⟨4204412461775957395643785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22423533129471772776766853 4204412461775957395643785)
                      ·
                        rfl

theorem cell23_8188064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_8188064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188064 prefixEnd_8188064 := by exact prefixLift 8188064
  have htrace : WordTrace (prefixWord ++ tailWord_8188064) baseStart_8188064 baseEnd_8188064 := by
    simpa [prefixWord, tailWord_8188064, baseEnd_8188064] using wordTrace_append hprefix tailTrace_8188064
  have hstable : (prefixWord ++ tailWord_8188064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188064).length < 2 ^ (prefixWord ++ tailWord_8188064).sum := by decide
  have hdescent : baseEnd_8188064 < baseStart_8188064 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188091 : List Nat := [1, 1, 1, 1, 1, 2, 7, 4, 1, 4]
def baseStart_8188091 : Nat := 118140960795 + 8188091 * 2 ^ 59
def prefixEnd_8188091 : Nat := 4983230072969 + 3 ^ 40 * 8188091 * 2
def baseEnd_8188091 : Nat := 1401475441917876263335387

theorem tailTrace_8188091 : CollatzResearch.WordTrace tailWord_8188091 prefixEnd_8188091 1401475441917876263335387 := by
  unfold tailWord_8188091
  simp only [CollatzResearch.WordTrace]
  refine ⟨298644213378952196454436127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199096142252634797636290751 298644213378952196454436127)
  ·
    refine ⟨447966320068428294681654191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298644213378952196454436127 447966320068428294681654191)
    ·
      refine ⟨671949480102642442022481287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447966320068428294681654191 671949480102642442022481287)
      ·
        refine ⟨1007924220153963663033721931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671949480102642442022481287 1007924220153963663033721931)
        ·
          refine ⟨1511886330230945494550582897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007924220153963663033721931 1511886330230945494550582897)
          ·
            refine ⟨1133914747673209120912937173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1511886330230945494550582897 1133914747673209120912937173)
            ·
              refine ⟨26576126898590838771396965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1133914747673209120912937173 26576126898590838771396965)
              ·
                refine ⟨4983023793485782269636931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26576126898590838771396965 4983023793485782269636931)
                ·
                  refine ⟨7474535690228673404455397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4983023793485782269636931 7474535690228673404455397)
                  ·
                    refine ⟨1401475441917876263335387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7474535690228673404455397 1401475441917876263335387)
                    ·
                      rfl

theorem cell23_8188091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 1, 4].length) (baseStart_8188091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188091 prefixEnd_8188091 := by exact prefixLift 8188091
  have htrace : WordTrace (prefixWord ++ tailWord_8188091) baseStart_8188091 baseEnd_8188091 := by
    simpa [prefixWord, tailWord_8188091, baseEnd_8188091] using wordTrace_append hprefix tailTrace_8188091
  have hstable : (prefixWord ++ tailWord_8188091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188091).length < 2 ^ (prefixWord ++ tailWord_8188091).sum := by decide
  have hdescent : baseEnd_8188091 < baseStart_8188091 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188108 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 3, 4]
def baseStart_8188108 : Nat := 118140960795 + 8188108 * 2 ^ 59
def prefixEnd_8188108 : Nat := 4983230072969 + 3 ^ 40 * 8188108 * 2
def baseEnd_8188108 : Nat := 1401478351641585074497861

theorem tailTrace_8188108 : CollatzResearch.WordTrace tailWord_8188108 prefixEnd_8188108 1401478351641585074497861 := by
  unfold tailWord_8188108
  simp only [CollatzResearch.WordTrace]
  refine ⟨149322416709945304178902489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199096555613260405571869985 149322416709945304178902489)
  ·
    refine ⟨111991812532458978134176867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149322416709945304178902489 111991812532458978134176867)
    ·
      refine ⟨167987718798688467201265301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111991812532458978134176867 167987718798688467201265301)
      ·
        refine ⟨7874424318688521900059311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167987718798688467201265301 7874424318688521900059311)
        ·
          refine ⟨11811636478032782850088967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7874424318688521900059311 11811636478032782850088967)
          ·
            refine ⟨17717454717049174275133451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11811636478032782850088967 17717454717049174275133451)
            ·
              refine ⟨26576182075573761412700177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17717454717049174275133451 26576182075573761412700177)
              ·
                refine ⟨19932136556680321059525133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26576182075573761412700177 19932136556680321059525133)
                ·
                  refine ⟨7474551208755120397321925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19932136556680321059525133 7474551208755120397321925)
                  ·
                    refine ⟨1401478351641585074497861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7474551208755120397321925 1401478351641585074497861)
                    ·
                      rfl

theorem cell23_8188108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_8188108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188108 prefixEnd_8188108 := by exact prefixLift 8188108
  have htrace : WordTrace (prefixWord ++ tailWord_8188108) baseStart_8188108 baseEnd_8188108 := by
    simpa [prefixWord, tailWord_8188108, baseEnd_8188108] using wordTrace_append hprefix tailTrace_8188108
  have hstable : (prefixWord ++ tailWord_8188108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188108).length < 2 ^ (prefixWord ++ tailWord_8188108).sum := by decide
  have hdescent : baseEnd_8188108 < baseStart_8188108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188118 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_8188118 : Nat := 118140960795 + 8188118 * 2 ^ 59
def prefixEnd_8188118 : Nat := 4983230072969 + 3 ^ 40 * 8188118 * 2
def baseEnd_8188118 : Nat := 4204440189731300184368537

theorem tailTrace_8188118 : CollatzResearch.WordTrace tailWord_8188118 prefixEnd_8188118 4204440189731300184368537 := by
  unfold tailWord_8188118
  simp only [CollatzResearch.WordTrace]
  refine ⟨18665324884365898754104313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199096798766569586710446005 18665324884365898754104313)
  ·
    refine ⟨13998993663274424065578235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18665324884365898754104313 13998993663274424065578235)
    ·
      refine ⟨20998490494911636098367353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13998993663274424065578235 20998490494911636098367353)
      ·
        refine ⟨15748867871183727073775515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20998490494911636098367353 15748867871183727073775515)
        ·
          refine ⟨23623301806775590610663273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15748867871183727073775515 23623301806775590610663273)
          ·
            refine ⟨17717476355081692957997455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23623301806775590610663273 17717476355081692957997455)
            ·
              refine ⟨26576214532622539436996183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17717476355081692957997455 26576214532622539436996183)
              ·
                refine ⟨39864321798933809155494275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26576214532622539436996183 39864321798933809155494275)
                ·
                  refine ⟨59796482698400713733241413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39864321798933809155494275 59796482698400713733241413)
                  ·
                    refine ⟨11211840505950133824982765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59796482698400713733241413 11211840505950133824982765)
                    ·
                      refine ⟨4204440189731300184368537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11211840505950133824982765 4204440189731300184368537)
                      ·
                        rfl

theorem cell23_8188118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_8188118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188118 prefixEnd_8188118 := by exact prefixLift 8188118
  have htrace : WordTrace (prefixWord ++ tailWord_8188118) baseStart_8188118 baseEnd_8188118 := by
    simpa [prefixWord, tailWord_8188118, baseEnd_8188118] using wordTrace_append hprefix tailTrace_8188118
  have hstable : (prefixWord ++ tailWord_8188118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188118).length < 2 ^ (prefixWord ++ tailWord_8188118).sum := by decide
  have hdescent : baseEnd_8188118 < baseStart_8188118 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188125 : List Nat := [1, 4, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_8188125 : Nat := 118140960795 + 8188125 * 2 ^ 59
def prefixEnd_8188125 : Nat := 4983230072969 + 3 ^ 40 * 8188125 * 2
def baseEnd_8188125 : Nat := 1401481261365293885660335

theorem tailTrace_8188125 : CollatzResearch.WordTrace tailWord_8188125 prefixEnd_8188125 1401481261365293885660335 := by
  unfold tailWord_8188125
  simp only [CollatzResearch.WordTrace]
  refine ⟨298645453460829020261173829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199096968973886013507449219 298645453460829020261173829)
  ·
    refine ⟨55996022523905441298970093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298645453460829020261173829 55996022523905441298970093)
    ·
      refine ⟨20998508446464540487113785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55996022523905441298970093 20998508446464540487113785)
      ·
        refine ⟨15748881334848405365335339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20998508446464540487113785 15748881334848405365335339)
        ·
          refine ⟨23623322002272608048003009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15748881334848405365335339 23623322002272608048003009)
          ·
            refine ⟨17717491501704456036002257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23623322002272608048003009 17717491501704456036002257)
            ·
              refine ⟨13288118626278342027001693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17717491501704456036002257 13288118626278342027001693)
              ·
                refine ⟨4983044484854378260125635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13288118626278342027001693 4983044484854378260125635)
                ·
                  refine ⟨7474566727281567390188453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4983044484854378260125635 7474566727281567390188453)
                  ·
                    refine ⟨1401481261365293885660335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7474566727281567390188453 1401481261365293885660335)
                    ·
                      rfl

theorem cell23_8188125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_8188125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188125 prefixEnd_8188125 := by exact prefixLift 8188125
  have htrace : WordTrace (prefixWord ++ tailWord_8188125) baseStart_8188125 baseEnd_8188125 := by
    simpa [prefixWord, tailWord_8188125, baseEnd_8188125] using wordTrace_append hprefix tailTrace_8188125
  have hstable : (prefixWord ++ tailWord_8188125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188125).length < 2 ^ (prefixWord ++ tailWord_8188125).sum := by decide
  have hdescent : baseEnd_8188125 < baseStart_8188125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188127 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 5]
def baseStart_8188127 : Nat := 118140960795 + 8188127 * 2 ^ 59
def prefixEnd_8188127 : Nat := 4983230072969 + 3 ^ 40 * 8188127 * 2
def baseEnd_8188127 : Nat := 4204444811057190649155995

theorem tailTrace_8188127 : CollatzResearch.WordTrace tailWord_8188127 prefixEnd_8188127 4204444811057190649155995 := by
  unfold tailWord_8188127
  simp only [CollatzResearch.WordTrace]
  refine ⟨298645526406821774602746635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199097017604547849735164423 298645526406821774602746635)
  ·
    refine ⟨447968289610232661904119953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298645526406821774602746635 447968289610232661904119953)
    ·
      refine ⟨335976217207674496428089965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447968289610232661904119953 335976217207674496428089965)
      ·
        refine ⟨125991081452877936160533737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335976217207674496428089965 125991081452877936160533737)
        ·
          refine ⟨94493311089658452120400303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125991081452877936160533737 94493311089658452120400303)
          ·
            refine ⟨141739966634487678180600455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94493311089658452120400303 141739966634487678180600455)
            ·
              refine ⟨212609949951731517270900683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141739966634487678180600455 212609949951731517270900683)
              ·
                refine ⟨318914924927597275906351025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212609949951731517270900683 318914924927597275906351025)
                ·
                  refine ⟨239186193695697956929763269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 318914924927597275906351025 239186193695697956929763269)
                  ·
                    refine ⟨44847411317943366924330613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239186193695697956929763269 44847411317943366924330613)
                    ·
                      refine ⟨4204444811057190649155995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44847411317943366924330613 4204444811057190649155995)
                      ·
                        rfl

theorem cell23_8188127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_8188127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188127 prefixEnd_8188127 := by exact prefixLift 8188127
  have htrace : WordTrace (prefixWord ++ tailWord_8188127) baseStart_8188127 baseEnd_8188127 := by
    simpa [prefixWord, tailWord_8188127, baseEnd_8188127] using wordTrace_append hprefix tailTrace_8188127
  have hstable : (prefixWord ++ tailWord_8188127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188127).length < 2 ^ (prefixWord ++ tailWord_8188127).sum := by decide
  have hdescent : baseEnd_8188127 < baseStart_8188127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188171 : List Nat := [1, 1, 1, 1, 5, 2, 4, 2, 1, 1, 4]
def baseStart_8188171 : Nat := 118140960795 + 8188171 * 2 ^ 59
def prefixEnd_8188171 : Nat := 4983230072969 + 3 ^ 40 * 8188171 * 2
def baseEnd_8188171 : Nat := 4204467404205988477005793

theorem tailTrace_8188171 : CollatzResearch.WordTrace tailWord_8188171 prefixEnd_8188171 4204467404205988477005793 := by
  unfold tailWord_8188171
  simp only [CollatzResearch.WordTrace]
  refine ⟨298647131218662370117348367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199098087479108246744898911 298647131218662370117348367)
  ·
    refine ⟨447970696827993555176022551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298647131218662370117348367 447970696827993555176022551)
    ·
      refine ⟨671956045241990332764033827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447970696827993555176022551 671956045241990332764033827)
      ·
        refine ⟨1007934067862985499146050741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671956045241990332764033827 1007934067862985499146050741)
        ·
          refine ⟨94493818862154890544942257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1007934067862985499146050741 94493818862154890544942257)
          ·
            refine ⟨70870364146616167908706693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94493818862154890544942257 70870364146616167908706693)
            ·
              refine ⟨13288193277490531482882505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70870364146616167908706693 13288193277490531482882505)
              ·
                refine ⟨9966144958117898612161879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13288193277490531482882505 9966144958117898612161879)
                ·
                  refine ⟨14949217437176847918242819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9966144958117898612161879 14949217437176847918242819)
                  ·
                    refine ⟨22423826155765271877364229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14949217437176847918242819 22423826155765271877364229)
                    ·
                      refine ⟨4204467404205988477005793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22423826155765271877364229 4204467404205988477005793)
                      ·
                        rfl

theorem cell23_8188171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 1, 4].length) (baseStart_8188171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188171 prefixEnd_8188171 := by exact prefixLift 8188171
  have htrace : WordTrace (prefixWord ++ tailWord_8188171) baseStart_8188171 baseEnd_8188171 := by
    simpa [prefixWord, tailWord_8188171, baseEnd_8188171] using wordTrace_append hprefix tailTrace_8188171
  have hstable : (prefixWord ++ tailWord_8188171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188171).length < 2 ^ (prefixWord ++ tailWord_8188171).sum := by decide
  have hdescent : baseEnd_8188171 < baseStart_8188171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188174 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_8188174 : Nat := 118140960795 + 8188174 * 2 ^ 59
def prefixEnd_8188174 : Nat := 4983230072969 + 3 ^ 40 * 8188174 * 2
def baseEnd_8188174 : Nat := 4204468944647951965268279

theorem tailTrace_8188174 : CollatzResearch.WordTrace tailWord_8188174 prefixEnd_8188174 4204468944647951965268279 := by
  unfold tailWord_8188174
  simp only [CollatzResearch.WordTrace]
  refine ⟨37330905079706437703713447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199098160425101001086471717 37330905079706437703713447)
  ·
    refine ⟨55996357619559656555570171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37330905079706437703713447 55996357619559656555570171)
    ·
      refine ⟨83994536429339484833355257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55996357619559656555570171 83994536429339484833355257)
      ·
        refine ⟨62995902322004613625016443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83994536429339484833355257 62995902322004613625016443)
        ·
          refine ⟨94493853483006920437524665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62995902322004613625016443 94493853483006920437524665)
          ·
            refine ⟨70870390112255190328143499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94493853483006920437524665 70870390112255190328143499)
            ·
              refine ⟨106305585168382785492215249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70870390112255190328143499 106305585168382785492215249)
              ·
                refine ⟨79729188876287089119161437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106305585168382785492215249 79729188876287089119161437)
                ·
                  refine ⟨29898445828607658419685539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79729188876287089119161437 29898445828607658419685539)
                  ·
                    refine ⟨44847668742911487629528309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29898445828607658419685539 44847668742911487629528309)
                    ·
                      refine ⟨4204468944647951965268279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44847668742911487629528309 4204468944647951965268279)
                      ·
                        rfl

theorem cell23_8188174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_8188174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188174 prefixEnd_8188174 := by exact prefixLift 8188174
  have htrace : WordTrace (prefixWord ++ tailWord_8188174) baseStart_8188174 baseEnd_8188174 := by
    simpa [prefixWord, tailWord_8188174, baseEnd_8188174] using wordTrace_append hprefix tailTrace_8188174
  have hstable : (prefixWord ++ tailWord_8188174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188174).length < 2 ^ (prefixWord ++ tailWord_8188174).sum := by decide
  have hdescent : baseEnd_8188174 < baseStart_8188174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188184 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_8188184 : Nat := 118140960795 + 8188184 * 2 ^ 59
def prefixEnd_8188184 : Nat := 4983230072969 + 3 ^ 40 * 8188184 * 2
def baseEnd_8188184 : Nat := 4204474079454496926143233

theorem tailTrace_8188184 : CollatzResearch.WordTrace tailWord_8188184 prefixEnd_8188184 4204474079454496926143233 := by
  unfold tailWord_8188184
  simp only [CollatzResearch.WordTrace]
  refine ⟨149323802683807636668785803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199098403578410182225047737 149323802683807636668785803)
  ·
    refine ⟨223985704025711455003178705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149323802683807636668785803 223985704025711455003178705)
    ·
      refine ⟨167989278019283591252384029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223985704025711455003178705 167989278019283591252384029)
      ·
        refine ⟨62995979257231346719644011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167989278019283591252384029 62995979257231346719644011)
        ·
          refine ⟨94493968885847020079466017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62995979257231346719644011 94493968885847020079466017)
          ·
            refine ⟨70870476664385265059599513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94493968885847020079466017 70870476664385265059599513)
            ·
              refine ⟨53152857498288948794699635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70870476664385265059599513 53152857498288948794699635)
              ·
                refine ⟨79729286247433423192049453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53152857498288948794699635 79729286247433423192049453)
                ·
                  refine ⟨29898482342787533697018545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79729286247433423192049453 29898482342787533697018545)
                  ·
                    refine ⟨22423861757090650272763909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29898482342787533697018545 22423861757090650272763909)
                    ·
                      refine ⟨4204474079454496926143233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22423861757090650272763909 4204474079454496926143233)
                      ·
                        rfl

theorem cell23_8188184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_8188184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188184 prefixEnd_8188184 := by exact prefixLift 8188184
  have htrace : WordTrace (prefixWord ++ tailWord_8188184) baseStart_8188184 baseEnd_8188184 := by
    simpa [prefixWord, tailWord_8188184, baseEnd_8188184] using wordTrace_append hprefix tailTrace_8188184
  have hstable : (prefixWord ++ tailWord_8188184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188184).length < 2 ^ (prefixWord ++ tailWord_8188184).sum := by decide
  have hdescent : baseEnd_8188184 < baseStart_8188184 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188191 : List Nat := [1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 5]
def baseStart_8188191 : Nat := 118140960795 + 8188191 * 2 ^ 59
def prefixEnd_8188191 : Nat := 4983230072969 + 3 ^ 40 * 8188191 * 2
def baseEnd_8188191 : Nat := 4204477673819078398755701

theorem tailTrace_8188191 : CollatzResearch.WordTrace tailWord_8188191 prefixEnd_8188191 4204477673819078398755701 := by
  unfold tailWord_8188191
  simp only [CollatzResearch.WordTrace]
  refine ⟨298647860678589913533076427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199098573785726609022050951 298647860678589913533076427)
  ·
    refine ⟨447971791017884870299614641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298647860678589913533076427 447971791017884870299614641)
    ·
      refine ⟨335978843263413652724710981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447971791017884870299614641 335978843263413652724710981)
      ·
        refine ⟨62996033111890059885883309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335978843263413652724710981 62996033111890059885883309)
        ·
          refine ⟨23623512416958772457206241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62996033111890059885883309 23623512416958772457206241)
          ·
            refine ⟨17717634312719079342904681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23623512416958772457206241 17717634312719079342904681)
            ·
              refine ⟨13288225734539309507178511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17717634312719079342904681 13288225734539309507178511)
              ·
                refine ⟨19932338601808964260767767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13288225734539309507178511 19932338601808964260767767)
                ·
                  refine ⟨29898507902713446391151651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19932338601808964260767767 29898507902713446391151651)
                  ·
                    refine ⟨44847761854070169586727477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29898507902713446391151651 44847761854070169586727477)
                    ·
                      refine ⟨4204477673819078398755701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44847761854070169586727477 4204477673819078398755701)
                      ·
                        rfl

theorem cell23_8188191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_8188191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188191 prefixEnd_8188191 := by exact prefixLift 8188191
  have htrace : WordTrace (prefixWord ++ tailWord_8188191) baseStart_8188191 baseEnd_8188191 := by
    simpa [prefixWord, tailWord_8188191, baseEnd_8188191] using wordTrace_append hprefix tailTrace_8188191
  have hstable : (prefixWord ++ tailWord_8188191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188191).length < 2 ^ (prefixWord ++ tailWord_8188191).sum := by decide
  have hdescent : baseEnd_8188191 < baseStart_8188191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188194 : List Nat := [3, 3, 1, 1, 3, 1, 11]
def baseStart_8188194 : Nat := 118140960795 + 8188194 * 2 ^ 59
def prefixEnd_8188194 : Nat := 4983230072969 + 3 ^ 40 * 8188194 * 2
def baseEnd_8188194 : Nat := 51907150793346196136027

theorem tailTrace_8188194 : CollatzResearch.WordTrace tailWord_8188194 prefixEnd_8188194 51907150793346196136027 := by
  unfold tailWord_8188194
  simp only [CollatzResearch.WordTrace]
  refine ⟨74661992524394761261358909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199098646731719363363623757 74661992524394761261358909)
  ·
    refine ⟨27998247196648035473009591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74661992524394761261358909 27998247196648035473009591)
    ·
      refine ⟨41997370794972053209514387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27998247196648035473009591 41997370794972053209514387)
      ·
        refine ⟨62996056192458079814271581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41997370794972053209514387 62996056192458079814271581)
        ·
          refine ⟨23623521072171779930351843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62996056192458079814271581 23623521072171779930351843)
          ·
            refine ⟨35435281608257669895527765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23623521072171779930351843 35435281608257669895527765)
            ·
              refine ⟨51907150793346196136027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35435281608257669895527765 51907150793346196136027)
              ·
                rfl

theorem cell23_8188194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 11].length) (baseStart_8188194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188194 prefixEnd_8188194 := by exact prefixLift 8188194
  have htrace : WordTrace (prefixWord ++ tailWord_8188194) baseStart_8188194 baseEnd_8188194 := by
    simpa [prefixWord, tailWord_8188194, baseEnd_8188194] using wordTrace_append hprefix tailTrace_8188194
  have hstable : (prefixWord ++ tailWord_8188194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188194).length < 2 ^ (prefixWord ++ tailWord_8188194).sum := by decide
  have hdescent : baseEnd_8188194 < baseStart_8188194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188199 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_8188199 : Nat := 118140960795 + 8188199 * 2 ^ 59
def prefixEnd_8188199 : Nat := 4983230072969 + 3 ^ 40 * 8188199 * 2
def baseEnd_8188199 : Nat := 4204481781664314367455665

theorem tailTrace_8188199 : CollatzResearch.WordTrace tailWord_8188199 prefixEnd_8188199 4204481781664314367455665 := by
  unfold tailWord_8188199
  simp only [CollatzResearch.WordTrace]
  refine ⟨298648152462560930899367651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199098768308373953932911767 298648152462560930899367651)
  ·
    refine ⟨447972228693841396349051477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298648152462560930899367651 447972228693841396349051477)
    ·
      refine ⟨5249674555005953863465447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 447972228693841396349051477 5249674555005953863465447)
      ·
        refine ⟨7874511832508930795198171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5249674555005953863465447 7874511832508930795198171)
        ·
          refine ⟨11811767748763396192797257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7874511832508930795198171 11811767748763396192797257)
          ·
            refine ⟨8858825811572547144597943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11811767748763396192797257 8858825811572547144597943)
            ·
              refine ⟨13288238717358820716896915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8858825811572547144597943 13288238717358820716896915)
              ·
                refine ⟨19932358076038231075345373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13288238717358820716896915 19932358076038231075345373)
                ·
                  refine ⟨7474634278514336653254515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19932358076038231075345373 7474634278514336653254515)
                  ·
                    refine ⟨11211951417771504979881773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7474634278514336653254515 11211951417771504979881773)
                    ·
                      refine ⟨4204481781664314367455665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11211951417771504979881773 4204481781664314367455665)
                      ·
                        rfl

theorem cell23_8188199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_8188199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188199 prefixEnd_8188199 := by exact prefixLift 8188199
  have htrace : WordTrace (prefixWord ++ tailWord_8188199) baseStart_8188199 baseEnd_8188199 := by
    simpa [prefixWord, tailWord_8188199, baseEnd_8188199] using wordTrace_append hprefix tailTrace_8188199
  have hstable : (prefixWord ++ tailWord_8188199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188199).length < 2 ^ (prefixWord ++ tailWord_8188199).sum := by decide
  have hdescent : baseEnd_8188199 < baseStart_8188199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188256 : List Nat := [2, 1, 1, 3, 6, 1, 2, 2, 1, 2, 2]
def baseStart_8188256 : Nat := 118140960795 + 8188256 * 2 ^ 59
def prefixEnd_8188256 : Nat := 4983230072969 + 3 ^ 40 * 8188256 * 2
def baseEnd_8188256 : Nat := 4204511050061620644442903

theorem tailTrace_8188256 : CollatzResearch.WordTrace tailWord_8188256 prefixEnd_8188256 4204511050061620644442903 := by
  unfold tailWord_8188256
  simp only [CollatzResearch.WordTrace]
  refine ⟨149325115711677214817096311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199100154282236286422795081 149325115711677214817096311)
  ·
    refine ⟨223987673567515822225644467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149325115711677214817096311 223987673567515822225644467)
    ·
      refine ⟨335981510351273733338466701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223987673567515822225644467 335981510351273733338466701)
      ·
        refine ⟨125993066381727650001925013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335981510351273733338466701 125993066381727650001925013)
        ·
          refine ⟨5905924986643483593840235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125993066381727650001925013 5905924986643483593840235)
          ·
            refine ⟨8858887479965225390760353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5905924986643483593840235 8858887479965225390760353)
            ·
              refine ⟨6644165609973919043070265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8858887479965225390760353 6644165609973919043070265)
              ·
                refine ⟨4983124207480439282302699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6644165609973919043070265 4983124207480439282302699)
                ·
                  refine ⟨7474686311220658923454049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4983124207480439282302699 7474686311220658923454049)
                  ·
                    refine ⟨5606014733415494192590537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7474686311220658923454049 5606014733415494192590537)
                    ·
                      refine ⟨4204511050061620644442903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606014733415494192590537 4204511050061620644442903)
                      ·
                        rfl

theorem cell23_8188256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_8188256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188256 prefixEnd_8188256 := by exact prefixLift 8188256
  have htrace : WordTrace (prefixWord ++ tailWord_8188256) baseStart_8188256 baseEnd_8188256 := by
    simpa [prefixWord, tailWord_8188256, baseEnd_8188256] using wordTrace_append hprefix tailTrace_8188256
  have hstable : (prefixWord ++ tailWord_8188256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188256).length < 2 ^ (prefixWord ++ tailWord_8188256).sum := by decide
  have hdescent : baseEnd_8188256 < baseStart_8188256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188311 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 3]
def baseStart_8188311 : Nat := 118140960795 + 8188311 * 2 ^ 59
def prefixEnd_8188311 : Nat := 4983230072969 + 3 ^ 40 * 8188311 * 2
def baseEnd_8188311 : Nat := 4204539291497617929255149

theorem tailTrace_8188311 : CollatzResearch.WordTrace tailWord_8188311 prefixEnd_8188311 4204539291497617929255149 := by
  unfold tailWord_8188311
  simp only [CollatzResearch.WordTrace]
  refine ⟨298652237438155174027444787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199101491625436782684963191 298652237438155174027444787)
  ·
    refine ⟨447978356157232761041167181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298652237438155174027444787 447978356157232761041167181)
    ·
      refine ⟨167991883558962285390437693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447978356157232761041167181 167991883558962285390437693)
      ·
        refine ⟨62996956334610857021414135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167991883558962285390437693 62996956334610857021414135)
        ·
          refine ⟨94495434501916285532121203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62996956334610857021414135 94495434501916285532121203)
          ·
            refine ⟨141743151752874428298181805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94495434501916285532121203 141743151752874428298181805)
            ·
              refine ⟨53153681907327910611818177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141743151752874428298181805 53153681907327910611818177)
              ·
                refine ⟨39865261430495932958863633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53153681907327910611818177 39865261430495932958863633)
                ·
                  refine ⟨29898946072871949719147725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39865261430495932958863633 29898946072871949719147725)
                  ·
                    refine ⟨11212104777326981144680397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29898946072871949719147725 11212104777326981144680397)
                    ·
                      refine ⟨4204539291497617929255149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11212104777326981144680397 4204539291497617929255149)
                      ·
                        rfl

theorem cell23_8188311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_8188311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188311 prefixEnd_8188311 := by exact prefixLift 8188311
  have htrace : WordTrace (prefixWord ++ tailWord_8188311) baseStart_8188311 baseEnd_8188311 := by
    simpa [prefixWord, tailWord_8188311, baseEnd_8188311] using wordTrace_append hprefix tailTrace_8188311
  have hstable : (prefixWord ++ tailWord_8188311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188311).length < 2 ^ (prefixWord ++ tailWord_8188311).sum := by decide
  have hdescent : baseEnd_8188311 < baseStart_8188311 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188312 : List Nat := [2, 1, 2, 5, 1, 1, 3, 2, 2, 2, 2]
def baseStart_8188312 : Nat := 118140960795 + 8188312 * 2 ^ 59
def prefixEnd_8188312 : Nat := 4983230072969 + 3 ^ 40 * 8188312 * 2
def baseEnd_8188312 : Nat := 4204539804978272425342645

theorem tailTrace_8188312 : CollatzResearch.WordTrace tailWord_8188312 prefixEnd_8188312 4204539804978272425342645 := by
  unfold tailWord_8188312
  simp only [CollatzResearch.WordTrace]
  refine ⟨149326136955575775599115595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199101515940767700798820793 149326136955575775599115595)
  ·
    refine ⟨223989205433363663398673393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149326136955575775599115595 223989205433363663398673393)
    ·
      refine ⟨167991904075022747549005045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223989205433363663398673393 167991904075022747549005045)
      ·
        refine ⟨15749241007033382582719223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167991904075022747549005045 15749241007033382582719223)
        ·
          refine ⟨23623861510550073874078835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15749241007033382582719223 23623861510550073874078835)
          ·
            refine ⟨35435792265825110811118253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23623861510550073874078835 35435792265825110811118253)
            ·
              refine ⟨13288422099684416554169345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35435792265825110811118253 13288422099684416554169345)
              ·
                refine ⟨9966316574763312415627009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13288422099684416554169345 9966316574763312415627009)
                ·
                  refine ⟨7474737431072484311720257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9966316574763312415627009 7474737431072484311720257)
                  ·
                    refine ⟨5606053073304363233790193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7474737431072484311720257 5606053073304363233790193)
                    ·
                      refine ⟨4204539804978272425342645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606053073304363233790193 4204539804978272425342645)
                      ·
                        rfl

theorem cell23_8188312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_8188312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188312 prefixEnd_8188312 := by exact prefixLift 8188312
  have htrace : WordTrace (prefixWord ++ tailWord_8188312) baseStart_8188312 baseEnd_8188312 := by
    simpa [prefixWord, tailWord_8188312, baseEnd_8188312] using wordTrace_append hprefix tailTrace_8188312
  have hstable : (prefixWord ++ tailWord_8188312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188312).length < 2 ^ (prefixWord ++ tailWord_8188312).sum := by decide
  have hdescent : baseEnd_8188312 < baseStart_8188312 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188318 : List Nat := [4, 3, 1, 2, 1, 1, 1, 3, 7]
def baseStart_8188318 : Nat := 118140960795 + 8188318 * 2 ^ 59
def prefixEnd_8188318 : Nat := 4983230072969 + 3 ^ 40 * 8188318 * 2
def baseEnd_8188318 : Nat := 467171431762466600207513

theorem tailTrace_8188318 : CollatzResearch.WordTrace tailWord_8188318 prefixEnd_8188318 467171431762466600207513 := by
  unfold tailWord_8188318
  simp only [CollatzResearch.WordTrace]
  refine ⟨37331561593641226777868701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199101661832753209481966405 37331561593641226777868701)
  ·
    refine ⟨13999335597615460041700763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37331561593641226777868701 13999335597615460041700763)
    ·
      refine ⟨20999003396423190062551145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13999335597615460041700763 20999003396423190062551145)
      ·
        refine ⟨15749252547317392546913359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20999003396423190062551145 15749252547317392546913359)
        ·
          refine ⟨23623878820976088820370039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15749252547317392546913359 23623878820976088820370039)
          ·
            refine ⟨35435818231464133230555059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23623878820976088820370039 35435818231464133230555059)
            ·
              refine ⟨53153727347196199845832589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35435818231464133230555059 53153727347196199845832589)
              ·
                refine ⟨19932647755198574942187221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53153727347196199845832589 19932647755198574942187221)
                ·
                  refine ⟨467171431762466600207513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19932647755198574942187221 467171431762466600207513)
                  ·
                    rfl

theorem cell23_8188318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_8188318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188318 prefixEnd_8188318 := by exact prefixLift 8188318
  have htrace : WordTrace (prefixWord ++ tailWord_8188318) baseStart_8188318 baseEnd_8188318 := by
    simpa [prefixWord, tailWord_8188318, baseEnd_8188318] using wordTrace_append hprefix tailTrace_8188318
  have hstable : (prefixWord ++ tailWord_8188318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188318).length < 2 ^ (prefixWord ++ tailWord_8188318).sum := by decide
  have hdescent : baseEnd_8188318 < baseStart_8188318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188344 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 1, 10]
def baseStart_8188344 : Nat := 118140960795 + 8188344 * 2 ^ 59
def prefixEnd_8188344 : Nat := 4983230072969 + 3 ^ 40 * 8188344 * 2
def baseEnd_8188344 : Nat := 1401518745453072100047499

theorem tailTrace_8188344 : CollatzResearch.WordTrace tailWord_8188344 prefixEnd_8188344 1401518745453072100047499 := by
  unfold tailWord_8188344
  simp only [CollatzResearch.WordTrace]
  refine ⟨149326720523517810331698043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199102294031357080442264057 149326720523517810331698043)
  ·
    refine ⟨223990080785276715497547065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149326720523517810331698043 223990080785276715497547065)
    ·
      refine ⟨167992560588957536623160299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223990080785276715497547065 167992560588957536623160299)
      ·
        refine ⟨251988840883436304934740449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167992560588957536623160299 251988840883436304934740449)
        ·
          refine ⟨188991630662577228701055337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251988840883436304934740449 188991630662577228701055337)
          ·
            refine ⟨141743722996932921525791503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188991630662577228701055337 141743722996932921525791503)
            ·
              refine ⟨212615584495399382288687255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141743722996932921525791503 212615584495399382288687255)
              ·
                refine ⟨318923376743099073433030883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212615584495399382288687255 318923376743099073433030883)
                ·
                  refine ⟨478385065114648610149546325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 318923376743099073433030883 478385065114648610149546325)
                  ·
                    refine ⟨1401518745453072100047499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 478385065114648610149546325 1401518745453072100047499)
                    ·
                      rfl

theorem cell23_8188344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_8188344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188344 prefixEnd_8188344 := by exact prefixLift 8188344
  have htrace : WordTrace (prefixWord ++ tailWord_8188344) baseStart_8188344 baseEnd_8188344 := by
    simpa [prefixWord, tailWord_8188344, baseEnd_8188344] using wordTrace_append hprefix tailTrace_8188344
  have hstable : (prefixWord ++ tailWord_8188344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188344).length < 2 ^ (prefixWord ++ tailWord_8188344).sum := by decide
  have hdescent : baseEnd_8188344 < baseStart_8188344 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188361 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 5, 4]
def baseStart_8188361 : Nat := 118140960795 + 8188361 * 2 ^ 59
def prefixEnd_8188361 : Nat := 4983230072969 + 3 ^ 40 * 8188361 * 2
def baseEnd_8188361 : Nat := 1401521655176780911209973

theorem tailTrace_8188361 : CollatzResearch.WordTrace tailWord_8188361 prefixEnd_8188361 1401521655176780911209973 := by
  unfold tailWord_8188361
  simp only [CollatzResearch.WordTrace]
  refine ⟨298654061087974032566764937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199102707391982688377843291 298654061087974032566764937)
  ·
    refine ⟨223990545815980524425073703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298654061087974032566764937 223990545815980524425073703)
    ·
      refine ⟨335985818723970786637610555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223990545815980524425073703 335985818723970786637610555)
      ·
        refine ⟨503978728085956179956415833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335985818723970786637610555 503978728085956179956415833)
        ·
          refine ⟨377984046064467134967311875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503978728085956179956415833 377984046064467134967311875)
          ·
            refine ⟨566976069096700702450967813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377984046064467134967311875 566976069096700702450967813)
            ·
              refine ⟨106308012955631381709556465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 566976069096700702450967813 106308012955631381709556465)
              ·
                refine ⟨79731009716723536282167349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106308012955631381709556465 79731009716723536282167349)
                ·
                  refine ⟨7474782160942831526453189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79731009716723536282167349 7474782160942831526453189)
                  ·
                    refine ⟨1401521655176780911209973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7474782160942831526453189 1401521655176780911209973)
                    ·
                      rfl

theorem cell23_8188361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 4].length) (baseStart_8188361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188361 prefixEnd_8188361 := by exact prefixLift 8188361
  have htrace : WordTrace (prefixWord ++ tailWord_8188361) baseStart_8188361 baseEnd_8188361 := by
    simpa [prefixWord, tailWord_8188361, baseEnd_8188361] using wordTrace_append hprefix tailTrace_8188361
  have hstable : (prefixWord ++ tailWord_8188361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188361).length < 2 ^ (prefixWord ++ tailWord_8188361).sum := by decide
  have hdescent : baseEnd_8188361 < baseStart_8188361 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188462 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_8188462 : Nat := 118140960795 + 8188462 * 2 ^ 59
def prefixEnd_8188462 : Nat := 4983230072969 + 3 ^ 40 * 8188462 * 2
def baseEnd_8188462 : Nat := 4204616827076446838466955

theorem tailTrace_8188462 : CollatzResearch.WordTrace tailWord_8188462 prefixEnd_8188462 4204616827076446838466955 := by
  unfold tailWord_8188462
  simp only [CollatzResearch.WordTrace]
  refine ⟨37332218107576015852023955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199105163240405417877461093 37332218107576015852023955)
  ·
    refine ⟨55998327161364023778035933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37332218107576015852023955 55998327161364023778035933)
    ·
      refine ⟨20999372685511508916763475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55998327161364023778035933 20999372685511508916763475)
      ·
        refine ⟨31499059028267263375145213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20999372685511508916763475 31499059028267263375145213)
        ·
          refine ⟨11812147135600223765679455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31499059028267263375145213 11812147135600223765679455)
          ·
            refine ⟨17718220703400335648519183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11812147135600223765679455 17718220703400335648519183)
            ·
              refine ⟨26577331055100503472778775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17718220703400335648519183 26577331055100503472778775)
              ·
                refine ⟨39865996582650755209168163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26577331055100503472778775 39865996582650755209168163)
                ·
                  refine ⟨59798994873976132813752245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39865996582650755209168163 59798994873976132813752245)
                  ·
                    refine ⟨5606155769435262451289273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59798994873976132813752245 5606155769435262451289273)
                    ·
                      refine ⟨4204616827076446838466955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606155769435262451289273 4204616827076446838466955)
                      ·
                        rfl

theorem cell23_8188462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_8188462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188462 prefixEnd_8188462 := by exact prefixLift 8188462
  have htrace : WordTrace (prefixWord ++ tailWord_8188462) baseStart_8188462 baseEnd_8188462 := by
    simpa [prefixWord, tailWord_8188462, baseEnd_8188462] using wordTrace_append hprefix tailTrace_8188462
  have hstable : (prefixWord ++ tailWord_8188462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188462).length < 2 ^ (prefixWord ++ tailWord_8188462).sum := by decide
  have hdescent : baseEnd_8188462 < baseStart_8188462 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188485 : List Nat := [1, 3, 1, 1, 1, 5, 3, 2, 2, 4]
def baseStart_8188485 : Nat := 118140960795 + 8188485 * 2 ^ 59
def prefixEnd_8188485 : Nat := 4983230072969 + 3 ^ 40 * 8188485 * 2
def baseEnd_8188485 : Nat := 1401542879043833416159783

theorem tailTrace_8188485 : CollatzResearch.WordTrace tailWord_8188485 prefixEnd_8188485 1401542879043833416159783 := by
  unfold tailWord_8188485
  simp only [CollatzResearch.WordTrace]
  refine ⟨298658583739524801744278909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199105722493016534496185939 298658583739524801744278909)
  ·
    refine ⟨111996968902321800654104591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298658583739524801744278909 111996968902321800654104591)
    ·
      refine ⟨167995453353482700981156887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111996968902321800654104591 167995453353482700981156887)
      ·
        refine ⟨251993180030224051471735331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167995453353482700981156887 251993180030224051471735331)
        ·
          refine ⟨377989770045336077207602997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251993180030224051471735331 377989770045336077207602997)
          ·
            refine ⟨35436540941750257238212781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 377989770045336077207602997 35436540941750257238212781)
            ·
              refine ⟨13288702853156346464329793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35436540941750257238212781 13288702853156346464329793)
              ·
                refine ⟨9966527139867259848247345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13288702853156346464329793 9966527139867259848247345)
                ·
                  refine ⟨7474895354900444886185509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9966527139867259848247345 7474895354900444886185509)
                  ·
                    refine ⟨1401542879043833416159783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7474895354900444886185509 1401542879043833416159783)
                    ·
                      rfl

theorem cell23_8188485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_8188485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188485 prefixEnd_8188485 := by exact prefixLift 8188485
  have htrace : WordTrace (prefixWord ++ tailWord_8188485) baseStart_8188485 baseEnd_8188485 := by
    simpa [prefixWord, tailWord_8188485, baseEnd_8188485] using wordTrace_append hprefix tailTrace_8188485
  have hstable : (prefixWord ++ tailWord_8188485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188485).length < 2 ^ (prefixWord ++ tailWord_8188485).sum := by decide
  have hdescent : baseEnd_8188485 < baseStart_8188485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188486 : List Nat := [6, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3]
def baseStart_8188486 : Nat := 118140960795 + 8188486 * 2 ^ 59
def prefixEnd_8188486 : Nat := 4983230072969 + 3 ^ 40 * 8188486 * 2
def baseEnd_8188486 : Nat := 4204629150612154744566845

theorem tailTrace_8188486 : CollatzResearch.WordTrace tailWord_8188486 prefixEnd_8188486 4204629150612154744566845 := by
  unfold tailWord_8188486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9333081881641286841095791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199105746808347452610043541 9333081881641286841095791)
  ·
    refine ⟨13999622822461930261643687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9333081881641286841095791 13999622822461930261643687)
    ·
      refine ⟨20999434233692895392465531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13999622822461930261643687 20999434233692895392465531)
      ·
        refine ⟨31499151350539343088698297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20999434233692895392465531 31499151350539343088698297)
        ·
          refine ⟨23624363512904507316523723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31499151350539343088698297 23624363512904507316523723)
          ·
            refine ⟨35436545269356760974785585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23624363512904507316523723 35436545269356760974785585)
            ·
              refine ⟨26577408952017570731089189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35436545269356760974785585 26577408952017570731089189)
              ·
                refine ⟨4983264178503294512079223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26577408952017570731089189 4983264178503294512079223)
                ·
                  refine ⟨7474896267754941768118835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4983264178503294512079223 7474896267754941768118835)
                  ·
                    refine ⟨11212344401632412652178253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7474896267754941768118835 11212344401632412652178253)
                    ·
                      refine ⟨4204629150612154744566845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11212344401632412652178253 4204629150612154744566845)
                      ·
                        rfl

theorem cell23_8188486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_8188486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188486 prefixEnd_8188486 := by exact prefixLift 8188486
  have htrace : WordTrace (prefixWord ++ tailWord_8188486) baseStart_8188486 baseEnd_8188486 := by
    simpa [prefixWord, tailWord_8188486, baseEnd_8188486] using wordTrace_append hprefix tailTrace_8188486
  have hstable : (prefixWord ++ tailWord_8188486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188486).length < 2 ^ (prefixWord ++ tailWord_8188486).sum := by decide
  have hdescent : baseEnd_8188486 < baseStart_8188486 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188492 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 3, 2, 2]
def baseStart_8188492 : Nat := 118140960795 + 8188492 * 2 ^ 59
def prefixEnd_8188492 : Nat := 4983230072969 + 3 ^ 40 * 8188492 * 2
def baseEnd_8188492 : Nat := 4204632231496081721091817

theorem tailTrace_8188492 : CollatzResearch.WordTrace tailWord_8188492 prefixEnd_8188492 4204632231496081721091817 := by
  unfold tailWord_8188492
  simp only [CollatzResearch.WordTrace]
  refine ⟨149329419525249720969891865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199105892700332961293189153 149329419525249720969891865)
  ·
    refine ⟨111997064643937290727418899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149329419525249720969891865 111997064643937290727418899)
    ·
      refine ⟨167995596965905936091128349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111997064643937290727418899 167995596965905936091128349)
      ·
        refine ⟨62998348862214726034173131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167995596965905936091128349 62998348862214726034173131)
        ·
          refine ⟨94497523293322089051259697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62998348862214726034173131 94497523293322089051259697)
          ·
            refine ⟨70873142469991566788444773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94497523293322089051259697 70873142469991566788444773)
            ·
              refine ⟨13288714213123418772833395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70873142469991566788444773 13288714213123418772833395)
              ·
                refine ⟨19933071319685128159250093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13288714213123418772833395 19933071319685128159250093)
                ·
                  refine ⟨7474901744881923059718785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19933071319685128159250093 7474901744881923059718785)
                  ·
                    refine ⟨5606176308661442294789089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7474901744881923059718785 5606176308661442294789089)
                    ·
                      refine ⟨4204632231496081721091817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606176308661442294789089 4204632231496081721091817)
                      ·
                        rfl

theorem cell23_8188492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_8188492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188492 prefixEnd_8188492 := by exact prefixLift 8188492
  have htrace : WordTrace (prefixWord ++ tailWord_8188492) baseStart_8188492 baseEnd_8188492 := by
    simpa [prefixWord, tailWord_8188492, baseEnd_8188492] using wordTrace_append hprefix tailTrace_8188492
  have hstable : (prefixWord ++ tailWord_8188492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188492).length < 2 ^ (prefixWord ++ tailWord_8188492).sum := by decide
  have hdescent : baseEnd_8188492 < baseStart_8188492 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188511 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 2, 7]
def baseStart_8188511 : Nat := 118140960795 + 8188511 * 2 ^ 59
def prefixEnd_8188511 : Nat := 4983230072969 + 3 ^ 40 * 8188511 * 2
def baseEnd_8188511 : Nat := 1401547329209505715584743

theorem tailTrace_8188511 : CollatzResearch.WordTrace tailWord_8188511 prefixEnd_8188511 1401547329209505715584743 := by
  unfold tailWord_8188511
  simp only [CollatzResearch.WordTrace]
  refine ⟨298659532037430608184725387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199106354691620405456483591 298659532037430608184725387)
  ·
    refine ⟨447989298056145912277088081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298659532037430608184725387 447989298056145912277088081)
    ·
      refine ⟨335991973542109434207816061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 447989298056145912277088081 335991973542109434207816061)
      ·
        refine ⟨125996990078291037827931023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335991973542109434207816061 125996990078291037827931023)
        ·
          refine ⟨188995485117436556741896535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125996990078291037827931023 188995485117436556741896535)
          ·
            refine ⟨283493227676154835112844803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188995485117436556741896535 283493227676154835112844803)
            ·
              refine ⟨425239841514232252669267205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283493227676154835112844803 425239841514232252669267205)
              ·
                refine ⟨79732470283918547375487601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425239841514232252669267205 79732470283918547375487601)
                ·
                  refine ⟨59799352712938910531615701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79732470283918547375487601 59799352712938910531615701)
                  ·
                    refine ⟨1401547329209505715584743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59799352712938910531615701 1401547329209505715584743)
                    ·
                      rfl

theorem cell23_8188511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 7].length) (baseStart_8188511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188511 prefixEnd_8188511 := by exact prefixLift 8188511
  have htrace : WordTrace (prefixWord ++ tailWord_8188511) baseStart_8188511 baseEnd_8188511 := by
    simpa [prefixWord, tailWord_8188511, baseEnd_8188511] using wordTrace_append hprefix tailTrace_8188511
  have hstable : (prefixWord ++ tailWord_8188511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188511).length < 2 ^ (prefixWord ++ tailWord_8188511).sum := by decide
  have hdescent : baseEnd_8188511 < baseStart_8188511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188526 : List Nat := [4, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_8188526 : Nat := 118140960795 + 8188526 * 2 ^ 59
def prefixEnd_8188526 : Nat := 4983230072969 + 3 ^ 40 * 8188526 * 2
def baseEnd_8188526 : Nat := 4204649689838334588066661

theorem tailTrace_8188526 : CollatzResearch.WordTrace tailWord_8188526 prefixEnd_8188526 4204649689838334588066661 := by
  unfold tailWord_8188526
  simp only [CollatzResearch.WordTrace]
  refine ⟨37332509891547033218315179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199106719421584177164347621 37332509891547033218315179)
  ·
    refine ⟨55998764837320549827472769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37332509891547033218315179 55998764837320549827472769)
    ·
      refine ⟨41999073627990412370604577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55998764837320549827472769 41999073627990412370604577)
      ·
        refine ⟨31499305220992809277953433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41999073627990412370604577 31499305220992809277953433)
        ·
          refine ⟨23624478915744606958465075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31499305220992809277953433 23624478915744606958465075)
          ·
            refine ⟨35436718373616910437697613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23624478915744606958465075 35436718373616910437697613)
            ·
              refine ⟨13288769390106341414136605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35436718373616910437697613 13288769390106341414136605)
              ·
                refine ⟨4983288521289878030301227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13288769390106341414136605 4983288521289878030301227)
                ·
                  refine ⟨7474932781934817045451841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4983288521289878030301227 7474932781934817045451841)
                  ·
                    refine ⟨5606199586451112784088881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7474932781934817045451841 5606199586451112784088881)
                    ·
                      refine ⟨4204649689838334588066661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606199586451112784088881 4204649689838334588066661)
                      ·
                        rfl

theorem cell23_8188526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_8188526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188526 prefixEnd_8188526 := by exact prefixLift 8188526
  have htrace : WordTrace (prefixWord ++ tailWord_8188526) baseStart_8188526 baseEnd_8188526 := by
    simpa [prefixWord, tailWord_8188526, baseEnd_8188526] using wordTrace_append hprefix tailTrace_8188526
  have hstable : (prefixWord ++ tailWord_8188526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188526).length < 2 ^ (prefixWord ++ tailWord_8188526).sum := by decide
  have hdescent : baseEnd_8188526 < baseStart_8188526 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188558 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_8188558 : Nat := 118140960795 + 8188558 * 2 ^ 59
def prefixEnd_8188558 : Nat := 4983230072969 + 3 ^ 40 * 8188558 * 2
def baseEnd_8188558 : Nat := 1401555373739759487622171

theorem tailTrace_8188558 : CollatzResearch.WordTrace tailWord_8188558 prefixEnd_8188558 1401555373739759487622171 := by
  unfold tailWord_8188558
  simp only [CollatzResearch.WordTrace]
  refine ⟨37332655783532541901460791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199107497512173556807790885 37332655783532541901460791)
  ·
    refine ⟨55998983675298812852191187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37332655783532541901460791 55998983675298812852191187)
    ·
      refine ⟨83998475512948219278286781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55998983675298812852191187 83998475512948219278286781)
      ·
        refine ⟨31499428317355582229357543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83998475512948219278286781 31499428317355582229357543)
        ·
          refine ⟨47249142476033373344036315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31499428317355582229357543 47249142476033373344036315)
          ·
            refine ⟨70873713714050060016054473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47249142476033373344036315 70873713714050060016054473)
            ·
              refine ⟨53155285285537545012040855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70873713714050060016054473 53155285285537545012040855)
              ·
                refine ⟨79732927928306317518061283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53155285285537545012040855 79732927928306317518061283)
                ·
                  refine ⟨119599391892459476277091925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79732927928306317518061283 119599391892459476277091925)
                  ·
                    refine ⟨1401555373739759487622171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119599391892459476277091925 1401555373739759487622171)
                    ·
                      rfl

theorem cell23_8188558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_8188558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188558 prefixEnd_8188558 := by exact prefixLift 8188558
  have htrace : WordTrace (prefixWord ++ tailWord_8188558) baseStart_8188558 baseEnd_8188558 := by
    simpa [prefixWord, tailWord_8188558, baseEnd_8188558] using wordTrace_append hprefix tailTrace_8188558
  have hstable : (prefixWord ++ tailWord_8188558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188558).length < 2 ^ (prefixWord ++ tailWord_8188558).sum := by decide
  have hdescent : baseEnd_8188558 < baseStart_8188558 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188568 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_8188568 : Nat := 118140960795 + 8188568 * 2 ^ 59
def prefixEnd_8188568 : Nat := 4983230072969 + 3 ^ 40 * 8188568 * 2
def baseEnd_8188568 : Nat := 4204671256025823423741467

theorem tailTrace_8188568 : CollatzResearch.WordTrace tailWord_8188568 prefixEnd_8188568 4204671256025823423741467 := by
  unfold tailWord_8188568
  simp only [CollatzResearch.WordTrace]
  refine ⟨149330805499112053459775179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199107740665482737946366905 149330805499112053459775179)
  ·
    refine ⟨223996208248668080189662769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149330805499112053459775179 223996208248668080189662769)
    ·
      refine ⟨167997156186501060142247077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223996208248668080189662769 167997156186501060142247077)
      ·
        refine ⟨31499466784968948776671327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167997156186501060142247077 31499466784968948776671327)
        ·
          refine ⟨47249200177453423165006991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31499466784968948776671327 47249200177453423165006991)
          ·
            refine ⟨70873800266180134747510487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47249200177453423165006991 70873800266180134747510487)
            ·
              refine ⟨106310700399270202121265731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70873800266180134747510487 106310700399270202121265731)
              ·
                refine ⟨159466050598905303181898597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106310700399270202121265731 159466050598905303181898597)
                ·
                  refine ⟨29899884487294744346605987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159466050598905303181898597 29899884487294744346605987)
                  ·
                    refine ⟨44849826730942116519908981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29899884487294744346605987 44849826730942116519908981)
                    ·
                      refine ⟨4204671256025823423741467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44849826730942116519908981 4204671256025823423741467)
                      ·
                        rfl

theorem cell23_8188568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_8188568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188568 prefixEnd_8188568 := by exact prefixLift 8188568
  have htrace : WordTrace (prefixWord ++ tailWord_8188568) baseStart_8188568 baseEnd_8188568 := by
    simpa [prefixWord, tailWord_8188568, baseEnd_8188568] using wordTrace_append hprefix tailTrace_8188568
  have hstable : (prefixWord ++ tailWord_8188568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188568).length < 2 ^ (prefixWord ++ tailWord_8188568).sum := by decide
  have hdescent : baseEnd_8188568 < baseStart_8188568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188571 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 13]
def baseStart_8188571 : Nat := 118140960795 + 8188571 * 2 ^ 59
def prefixEnd_8188571 : Nat := 4983230072969 + 3 ^ 40 * 8188571 * 2
def baseEnd_8188571 : Nat := 467185866274198545778217

theorem tailTrace_8188571 : CollatzResearch.WordTrace tailWord_8188571 prefixEnd_8188571 467185866274198545778217 := by
  unfold tailWord_8188571
  simp only [CollatzResearch.WordTrace]
  refine ⟨298661720417213238431909567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199107813611475492287939711 298661720417213238431909567)
  ·
    refine ⟨447992580625819857647864351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298661720417213238431909567 447992580625819857647864351)
    ·
      refine ⟨671988870938729786471796527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447992580625819857647864351 671988870938729786471796527)
      ·
        refine ⟨1007983306408094679707694791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671988870938729786471796527 1007983306408094679707694791)
        ·
          refine ⟨1511974959612142019561542187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007983306408094679707694791 1511974959612142019561542187)
          ·
            refine ⟨2267962439418213029342313281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511974959612142019561542187 2267962439418213029342313281)
            ·
              refine ⟨1700971829563659772006734961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2267962439418213029342313281 1700971829563659772006734961)
              ·
                refine ⟨1275728872172744829005051221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1700971829563659772006734961 1275728872172744829005051221)
                ·
                  refine ⟨467185866274198545778217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 1275728872172744829005051221 467185866274198545778217)
                  ·
                    rfl

theorem cell23_8188571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 13].length) (baseStart_8188571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188571 prefixEnd_8188571 := by exact prefixLift 8188571
  have htrace : WordTrace (prefixWord ++ tailWord_8188571) baseStart_8188571 baseEnd_8188571 := by
    simpa [prefixWord, tailWord_8188571, baseEnd_8188571] using wordTrace_append hprefix tailTrace_8188571
  have hstable : (prefixWord ++ tailWord_8188571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188571).length < 2 ^ (prefixWord ++ tailWord_8188571).sum := by decide
  have hdescent : baseEnd_8188571 < baseStart_8188571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188625 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 2, 5, 2]
def baseStart_8188625 : Nat := 118140960795 + 8188625 * 2 ^ 59
def prefixEnd_8188625 : Nat := 4983230072969 + 3 ^ 40 * 8188625 * 2
def baseEnd_8188625 : Nat := 4204700524423129700728705

theorem tailTrace_8188625 : CollatzResearch.WordTrace tailWord_8188625 prefixEnd_8188625 4204700524423129700728705 := by
  unfold tailWord_8188625
  simp only [CollatzResearch.WordTrace]
  refine ⟨298663689959017605654375329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199109126639345070436250219 298663689959017605654375329)
  ·
    refine ⟨223997767469263204240781497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298663689959017605654375329 223997767469263204240781497)
    ·
      refine ⟨167998325601947403180586123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223997767469263204240781497 167998325601947403180586123)
      ·
        refine ⟨251997488402921104770879185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167998325601947403180586123 251997488402921104770879185)
        ·
          refine ⟨188998116302190828578159389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251997488402921104770879185 188998116302190828578159389)
          ·
            refine ⟨70874293613321560716809771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188998116302190828578159389 70874293613321560716809771)
            ·
              refine ⟨106311440419982341075214657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70874293613321560716809771 106311440419982341075214657)
              ·
                refine ⟨79733580314986755806410993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106311440419982341075214657 79733580314986755806410993)
                ·
                  refine ⟨59800185236240066854808245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79733580314986755806410993 59800185236240066854808245)
                  ·
                    refine ⟨5606267365897506267638273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59800185236240066854808245 5606267365897506267638273)
                    ·
                      refine ⟨4204700524423129700728705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606267365897506267638273 4204700524423129700728705)
                      ·
                        rfl

theorem cell23_8188625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 5, 2].length) (baseStart_8188625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188625 prefixEnd_8188625 := by exact prefixLift 8188625
  have htrace : WordTrace (prefixWord ++ tailWord_8188625) baseStart_8188625 baseEnd_8188625 := by
    simpa [prefixWord, tailWord_8188625, baseEnd_8188625] using wordTrace_append hprefix tailTrace_8188625
  have hstable : (prefixWord ++ tailWord_8188625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188625).length < 2 ^ (prefixWord ++ tailWord_8188625).sum := by decide
  have hdescent : baseEnd_8188625 < baseStart_8188625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188732 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 6, 3, 2]
def baseStart_8188732 : Nat := 118140960795 + 8188732 * 2 ^ 59
def prefixEnd_8188732 : Nat := 4983230072969 + 3 ^ 40 * 8188732 * 2
def baseEnd_8188732 : Nat := 4204755466853160782090713

theorem tailTrace_8188732 : CollatzResearch.WordTrace tailWord_8188732 prefixEnd_8188732 4204755466853160782090713 := by
  unfold tailWord_8188732
  simp only [CollatzResearch.WordTrace]
  refine ⟨149333796284814981464260225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199111728379753308619013633 149333796284814981464260225)
  ·
    refine ⟨112000347213611236098195169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149333796284814981464260225 112000347213611236098195169)
    ·
      refine ⟨84000260410208427073646377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112000347213611236098195169 84000260410208427073646377)
      ·
        refine ⟨63000195307656320305234783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84000260410208427073646377 63000195307656320305234783)
        ·
          refine ⟨94500292961484480457852175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63000195307656320305234783 94500292961484480457852175)
          ·
            refine ⟨141750439442226720686778263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94500292961484480457852175 141750439442226720686778263)
            ·
              refine ⟨212625659163340081030167395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141750439442226720686778263 212625659163340081030167395)
              ·
                refine ⟨318938488745010121545251093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212625659163340081030167395 318938488745010121545251093)
                ·
                  refine ⟨14950241659922349447433645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 318938488745010121545251093 14950241659922349447433645)
                  ·
                    refine ⟨5606340622470881042787617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14950241659922349447433645 5606340622470881042787617)
                    ·
                      refine ⟨4204755466853160782090713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606340622470881042787617 4204755466853160782090713)
                      ·
                        rfl

theorem cell23_8188732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_8188732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188732 prefixEnd_8188732 := by exact prefixLift 8188732
  have htrace : WordTrace (prefixWord ++ tailWord_8188732) baseStart_8188732 baseEnd_8188732 := by
    simpa [prefixWord, tailWord_8188732, baseEnd_8188732] using wordTrace_append hprefix tailTrace_8188732
  have hstable : (prefixWord ++ tailWord_8188732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188732).length < 2 ^ (prefixWord ++ tailWord_8188732).sum := by decide
  have hdescent : baseEnd_8188732 < baseStart_8188732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188755 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 6, 4]
def baseStart_8188755 : Nat := 118140960795 + 8188755 * 2 ^ 59
def prefixEnd_8188755 : Nat := 4983230072969 + 3 ^ 40 * 8188755 * 2
def baseEnd_8188755 : Nat := 1401589092302738064034369

theorem tailTrace_8188755 : CollatzResearch.WordTrace tailWord_8188755 prefixEnd_8188755 1401589092302738064034369 := by
  unfold tailWord_8188755
  simp only [CollatzResearch.WordTrace]
  refine ⟨298668431448546637856607719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199112287632364425237738479 298668431448546637856607719)
  ·
    refine ⟨448002647172819956784911579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298668431448546637856607719 448002647172819956784911579)
    ·
      refine ⟨672003970759229935177367369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448002647172819956784911579 672003970759229935177367369)
      ·
        refine ⟨504002978069422451383025527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672003970759229935177367369 504002978069422451383025527)
        ·
          refine ⟨756004467104133677074538291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504002978069422451383025527 756004467104133677074538291)
          ·
            refine ⟨1134006700656200515611807437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756004467104133677074538291 1134006700656200515611807437)
            ·
              refine ⟨425252512746075193354427789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1134006700656200515611807437 425252512746075193354427789)
              ·
                refine ⟨159469692279778197507910421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 425252512746075193354427789 159469692279778197507910421)
                ·
                  refine ⟨7475141825614603008183301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159469692279778197507910421 7475141825614603008183301)
                  ·
                    refine ⟨1401589092302738064034369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7475141825614603008183301 1401589092302738064034369)
                    ·
                      rfl

theorem cell23_8188755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 4].length) (baseStart_8188755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188755 prefixEnd_8188755 := by exact prefixLift 8188755
  have htrace : WordTrace (prefixWord ++ tailWord_8188755) baseStart_8188755 baseEnd_8188755 := by
    simpa [prefixWord, tailWord_8188755, baseEnd_8188755] using wordTrace_append hprefix tailTrace_8188755
  have hstable : (prefixWord ++ tailWord_8188755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188755).length < 2 ^ (prefixWord ++ tailWord_8188755).sum := by decide
  have hdescent : baseEnd_8188755 < baseStart_8188755 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188759 : List Nat := [1, 1, 3, 2, 4, 2, 3, 1, 1, 5]
def baseStart_8188759 : Nat := 118140960795 + 8188759 * 2 ^ 59
def prefixEnd_8188759 : Nat := 4983230072969 + 3 ^ 40 * 8188759 * 2
def baseEnd_8188759 : Nat := 1401589776943610725484363

theorem tailTrace_8188759 : CollatzResearch.WordTrace tailWord_8188759 prefixEnd_8188759 1401589776943610725484363 := by
  unfold tailWord_8188759
  simp only [CollatzResearch.WordTrace]
  refine ⟨298668577340532146539753331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199112384893688097693168887 298668577340532146539753331)
  ·
    refine ⟨448002866010798219809629997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298668577340532146539753331 448002866010798219809629997)
    ·
      refine ⟨168001074754049332428611249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448002866010798219809629997 168001074754049332428611249)
      ·
        refine ⟨126000806065536999321458437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168001074754049332428611249 126000806065536999321458437)
        ·
          refine ⟨23625151137288187372773457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126000806065536999321458437 23625151137288187372773457)
          ·
            refine ⟨17718863352966140529580093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23625151137288187372773457 17718863352966140529580093)
            ·
              refine ⟨6644573757362302698592535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17718863352966140529580093 6644573757362302698592535)
              ·
                refine ⟨9966860636043454047888803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6644573757362302698592535 9966860636043454047888803)
                ·
                  refine ⟨14950290954065181071833205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9966860636043454047888803 14950290954065181071833205)
                  ·
                    refine ⟨1401589776943610725484363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14950290954065181071833205 1401589776943610725484363)
                    ·
                      rfl

theorem cell23_8188759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_8188759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188759 prefixEnd_8188759 := by exact prefixLift 8188759
  have htrace : WordTrace (prefixWord ++ tailWord_8188759) baseStart_8188759 baseEnd_8188759 := by
    simpa [prefixWord, tailWord_8188759, baseEnd_8188759] using wordTrace_append hprefix tailTrace_8188759
  have hstable : (prefixWord ++ tailWord_8188759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188759).length < 2 ^ (prefixWord ++ tailWord_8188759).sum := by decide
  have hdescent : baseEnd_8188759 < baseStart_8188759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188785 : List Nat := [1, 2, 2, 2, 1, 4, 3, 8]
def baseStart_8188785 : Nat := 118140960795 + 8188785 * 2 ^ 59
def prefixEnd_8188785 : Nat := 4983230072969 + 3 ^ 40 * 8188785 * 2
def baseEnd_8188785 : Nat := 155732691901031447212147

theorem tailTrace_8188785 : CollatzResearch.WordTrace tailWord_8188785 prefixEnd_8188785 155732691901031447212147 := by
  unfold tailWord_8188785
  simp only [CollatzResearch.WordTrace]
  refine ⟨298669525638437952980199809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199113017092291968653466539 298669525638437952980199809)
  ·
    refine ⟨224002144228828464735149857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298669525638437952980199809 224002144228828464735149857)
    ·
      refine ⟨168001608171621348551362393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224002144228828464735149857 168001608171621348551362393)
      ·
        refine ⟨126001206128716011413521795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168001608171621348551362393 126001206128716011413521795)
        ·
          refine ⟨189001809193074017120282693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126001206128716011413521795 189001809193074017120282693)
          ·
            refine ⟨35437839223701378210053005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189001809193074017120282693 35437839223701378210053005)
            ·
              refine ⟨13289189708888016828769877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35437839223701378210053005 13289189708888016828769877)
              ·
                refine ⟨155732691901031447212147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13289189708888016828769877 155732691901031447212147)
                ·
                  rfl

theorem cell23_8188785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 8].length) (baseStart_8188785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188785 prefixEnd_8188785 := by exact prefixLift 8188785
  have htrace : WordTrace (prefixWord ++ tailWord_8188785) baseStart_8188785 baseEnd_8188785 := by
    simpa [prefixWord, tailWord_8188785, baseEnd_8188785] using wordTrace_append hprefix tailTrace_8188785
  have hstable : (prefixWord ++ tailWord_8188785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188785).length < 2 ^ (prefixWord ++ tailWord_8188785).sum := by decide
  have hdescent : baseEnd_8188785 < baseStart_8188785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188789 : List Nat := [1, 3, 4, 1, 1, 2, 2, 3, 2, 4]
def baseStart_8188789 : Nat := 118140960795 + 8188789 * 2 ^ 59
def prefixEnd_8188789 : Nat := 4983230072969 + 3 ^ 40 * 8188789 * 2
def baseEnd_8188789 : Nat := 1401594911750155686359317

theorem tailTrace_8188789 : CollatzResearch.WordTrace tailWord_8188789 prefixEnd_8188789 1401594911750155686359317 := by
  unfold tailWord_8188789
  simp only [CollatzResearch.WordTrace]
  refine ⟨298669671530423461663345421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199113114353615641108896947 298669671530423461663345421)
  ·
    refine ⟨112001126823908798123754533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298669671530423461663345421 112001126823908798123754533)
    ·
      refine ⟨21000211279482899648203975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112001126823908798123754533 21000211279482899648203975)
      ·
        refine ⟨31500316919224349472305963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21000211279482899648203975 31500316919224349472305963)
        ·
          refine ⟨47250475378836524208458945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31500316919224349472305963 47250475378836524208458945)
          ·
            refine ⟨35437856534127393156344209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47250475378836524208458945 35437856534127393156344209)
            ·
              refine ⟨26578392400595544867258157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35437856534127393156344209 26578392400595544867258157)
              ·
                refine ⟨9966897150223329325221809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26578392400595544867258157 9966897150223329325221809)
                ·
                  refine ⟨7475172862667496993916357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9966897150223329325221809 7475172862667496993916357)
                  ·
                    refine ⟨1401594911750155686359317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7475172862667496993916357 1401594911750155686359317)
                    ·
                      rfl

theorem cell23_8188789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_8188789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188789 prefixEnd_8188789 := by exact prefixLift 8188789
  have htrace : WordTrace (prefixWord ++ tailWord_8188789) baseStart_8188789 baseEnd_8188789 := by
    simpa [prefixWord, tailWord_8188789, baseEnd_8188789] using wordTrace_append hprefix tailTrace_8188789
  have hstable : (prefixWord ++ tailWord_8188789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188789).length < 2 ^ (prefixWord ++ tailWord_8188789).sum := by decide
  have hdescent : baseEnd_8188789 < baseStart_8188789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188812 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 1, 3, 3]
def baseStart_8188812 : Nat := 118140960795 + 8188812 * 2 ^ 59
def prefixEnd_8188812 : Nat := 4983230072969 + 3 ^ 40 * 8188812 * 2
def baseEnd_8188812 : Nat := 4204796545305520469090345

theorem tailTrace_8188812 : CollatzResearch.WordTrace tailWord_8188812 prefixEnd_8188812 4204796545305520469090345 := by
  unfold tailWord_8188812
  simp only [CollatzResearch.WordTrace]
  refine ⟨149335255204670068295716345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199113673606226757727621793 149335255204670068295716345)
  ·
    refine ⟨112001441403502551221787259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149335255204670068295716345 112001441403502551221787259)
    ·
      refine ⟨168002162105253826832680889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112001441403502551221787259 168002162105253826832680889)
      ·
        refine ⟨126001621578940370124510667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168002162105253826832680889 126001621578940370124510667)
        ·
          refine ⟨189002432368410555186766001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126001621578940370124510667 189002432368410555186766001)
          ·
            refine ⟨141751824276307916390074501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189002432368410555186766001 141751824276307916390074501)
            ·
              refine ⟨26578467051807734323138969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141751824276307916390074501 26578467051807734323138969)
              ·
                refine ⟨19933850288855800742354227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26578467051807734323138969 19933850288855800742354227)
                ·
                  refine ⟨29900775433283701113531341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19933850288855800742354227 29900775433283701113531341)
                  ·
                    refine ⟨11212790787481387917574253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29900775433283701113531341 11212790787481387917574253)
                    ·
                      refine ⟨4204796545305520469090345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11212790787481387917574253 4204796545305520469090345)
                      ·
                        rfl

theorem cell23_8188812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_8188812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188812 prefixEnd_8188812 := by exact prefixLift 8188812
  have htrace : WordTrace (prefixWord ++ tailWord_8188812) baseStart_8188812 baseEnd_8188812 := by
    simpa [prefixWord, tailWord_8188812, baseEnd_8188812] using wordTrace_append hprefix tailTrace_8188812
  have hstable : (prefixWord ++ tailWord_8188812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188812).length < 2 ^ (prefixWord ++ tailWord_8188812).sum := by decide
  have hdescent : baseEnd_8188812 < baseStart_8188812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188829 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_8188829 : Nat := 118140960795 + 8188829 * 2 ^ 59
def prefixEnd_8188829 : Nat := 4983230072969 + 3 ^ 40 * 8188829 * 2
def baseEnd_8188829 : Nat := 4204805274476646902577767

theorem tailTrace_8188829 : CollatzResearch.WordTrace tailWord_8188829 prefixEnd_8188829 4204805274476646902577767 := by
  unfold tailWord_8188829
  simp only [CollatzResearch.WordTrace]
  refine ⟨298671130450278548494801541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199114086966852365663201027 298671130450278548494801541)
  ·
    refine ⟨56000836959427227842775289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298671130450278548494801541 56000836959427227842775289)
    ·
      refine ⟨42000627719570420882081467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56000836959427227842775289 42000627719570420882081467)
      ·
        refine ⟨63000941579355631323122201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42000627719570420882081467 63000941579355631323122201)
        ·
          refine ⟨47250706184516723492341651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63000941579355631323122201 47250706184516723492341651)
          ·
            refine ⟨70876059276775085238512477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47250706184516723492341651 70876059276775085238512477)
            ·
              refine ⟨26578522228790656964442179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70876059276775085238512477 26578522228790656964442179)
              ·
                refine ⟨39867783343185985446663269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26578522228790656964442179 39867783343185985446663269)
                ·
                  refine ⟨7475209376847372271249363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39867783343185985446663269 7475209376847372271249363)
                  ·
                    refine ⟨11212814065271058406874045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7475209376847372271249363 11212814065271058406874045)
                    ·
                      refine ⟨4204805274476646902577767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11212814065271058406874045 4204805274476646902577767)
                      ·
                        rfl

theorem cell23_8188829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_8188829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188829 prefixEnd_8188829 := by exact prefixLift 8188829
  have htrace : WordTrace (prefixWord ++ tailWord_8188829) baseStart_8188829 baseEnd_8188829 := by
    simpa [prefixWord, tailWord_8188829, baseEnd_8188829] using wordTrace_append hprefix tailTrace_8188829
  have hstable : (prefixWord ++ tailWord_8188829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188829).length < 2 ^ (prefixWord ++ tailWord_8188829).sum := by decide
  have hdescent : baseEnd_8188829 < baseStart_8188829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188835 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 4]
def baseStart_8188835 : Nat := 118140960795 + 8188835 * 2 ^ 59
def prefixEnd_8188835 : Nat := 4983230072969 + 3 ^ 40 * 8188835 * 2
def baseEnd_8188835 : Nat := 4204808355360573879102739

theorem tailTrace_8188835 : CollatzResearch.WordTrace tailWord_8188835 prefixEnd_8188835 4204808355360573879102739 := by
  unfold tailWord_8188835
  simp only [CollatzResearch.WordTrace]
  refine ⟨298671349288256811519519959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199114232858837874346346639 298671349288256811519519959)
  ·
    refine ⟨448007023932385217279279939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298671349288256811519519959 448007023932385217279279939)
    ·
      refine ⟨672010535898577825918919909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448007023932385217279279939 672010535898577825918919909)
      ·
        refine ⟨126001975480983342359797483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 672010535898577825918919909 126001975480983342359797483)
        ·
          refine ⟨189002963221475013539696225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126001975480983342359797483 189002963221475013539696225)
          ·
            refine ⟨141752222416106260154772169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189002963221475013539696225 141752222416106260154772169)
            ·
              refine ⟨106314166812079695116079127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141752222416106260154772169 106314166812079695116079127)
              ·
                refine ⟨159471250218119542674118691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106314166812079695116079127 159471250218119542674118691)
                ·
                  refine ⟨239206875327179314011178037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159471250218119542674118691 239206875327179314011178037)
                  ·
                    refine ⟨22425644561923060688547941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 239206875327179314011178037 22425644561923060688547941)
                    ·
                      refine ⟨4204808355360573879102739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22425644561923060688547941 4204808355360573879102739)
                      ·
                        rfl

theorem cell23_8188835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_8188835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188835 prefixEnd_8188835 := by exact prefixLift 8188835
  have htrace : WordTrace (prefixWord ++ tailWord_8188835) baseStart_8188835 baseEnd_8188835 := by
    simpa [prefixWord, tailWord_8188835, baseEnd_8188835] using wordTrace_append hprefix tailTrace_8188835
  have hstable : (prefixWord ++ tailWord_8188835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188835).length < 2 ^ (prefixWord ++ tailWord_8188835).sum := by decide
  have hdescent : baseEnd_8188835 < baseStart_8188835 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188856 : List Nat := [2, 1, 2, 1, 2, 5, 2, 2, 1, 3, 2]
def baseStart_8188856 : Nat := 118140960795 + 8188856 * 2 ^ 59
def prefixEnd_8188856 : Nat := 4983230072969 + 3 ^ 40 * 8188856 * 2
def baseEnd_8188856 : Nat := 4204819138454318296940143

theorem tailTrace_8188856 : CollatzResearch.WordTrace tailWord_8188856 prefixEnd_8188856 4204819138454318296940143 := by
  unfold tailWord_8188856
  simp only [CollatzResearch.WordTrace]
  refine ⟨149336057610590366053017211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199114743480787154737356281 149336057610590366053017211)
  ·
    refine ⟨224004086415885549079525817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149336057610590366053017211 224004086415885549079525817)
    ·
      refine ⟨168003064811914161809644363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224004086415885549079525817 168003064811914161809644363)
      ·
        refine ⟨252004597217871242714466545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168003064811914161809644363 252004597217871242714466545)
        ·
          refine ⟨189003447913403432035849909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252004597217871242714466545 189003447913403432035849909)
          ·
            refine ⟨17719073241881571753360929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189003447913403432035849909 17719073241881571753360929)
            ·
              refine ⟨13289304931411178815020697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17719073241881571753360929 13289304931411178815020697)
              ·
                refine ⟨9966978698558384111265523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13289304931411178815020697 9966978698558384111265523)
                ·
                  refine ⟨14950468047837576166898285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9966978698558384111265523 14950468047837576166898285)
                  ·
                    refine ⟨5606425517939091062586857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14950468047837576166898285 5606425517939091062586857)
                    ·
                      refine ⟨4204819138454318296940143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606425517939091062586857 4204819138454318296940143)
                      ·
                        rfl

theorem cell23_8188856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 1, 3, 2].length) (baseStart_8188856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188856 prefixEnd_8188856 := by exact prefixLift 8188856
  have htrace : WordTrace (prefixWord ++ tailWord_8188856) baseStart_8188856 baseEnd_8188856 := by
    simpa [prefixWord, tailWord_8188856, baseEnd_8188856] using wordTrace_append hprefix tailTrace_8188856
  have hstable : (prefixWord ++ tailWord_8188856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188856).length < 2 ^ (prefixWord ++ tailWord_8188856).sum := by decide
  have hdescent : baseEnd_8188856 < baseStart_8188856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188870 : List Nat := [6, 1, 3, 1, 2, 1, 9]
def baseStart_8188870 : Nat := 118140960795 + 8188870 * 2 ^ 59
def prefixEnd_8188870 : Nat := 4983230072969 + 3 ^ 40 * 8188870 * 2
def baseEnd_8188870 : Nat := 51911436138067669656359

theorem tailTrace_8188870 : CollatzResearch.WordTrace tailWord_8188870 prefixEnd_8188870 51911436138067669656359 := by
  unfold tailWord_8188870
  simp only [CollatzResearch.WordTrace]
  refine ⟨9333519557597812890532627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199115083895420008331362709 9333519557597812890532627)
  ·
    refine ⟨14000279336396719335798941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9333519557597812890532627 14000279336396719335798941)
    ·
      refine ⟨5250104751148769750924603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14000279336396719335798941 5250104751148769750924603)
      ·
        refine ⟨7875157126723154626386905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250104751148769750924603 7875157126723154626386905)
        ·
          refine ⟨5906367845042365969790179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7875157126723154626386905 5906367845042365969790179)
          ·
            refine ⟨8859551767563548954685269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5906367845042365969790179 8859551767563548954685269)
            ·
              refine ⟨51911436138067669656359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8859551767563548954685269 51911436138067669656359)
              ·
                rfl

theorem cell23_8188870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 9].length) (baseStart_8188870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188870 prefixEnd_8188870 := by exact prefixLift 8188870
  have htrace : WordTrace (prefixWord ++ tailWord_8188870) baseStart_8188870 baseEnd_8188870 := by
    simpa [prefixWord, tailWord_8188870, baseEnd_8188870] using wordTrace_append hprefix tailTrace_8188870
  have hstable : (prefixWord ++ tailWord_8188870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188870).length < 2 ^ (prefixWord ++ tailWord_8188870).sum := by decide
  have hdescent : baseEnd_8188870 < baseStart_8188870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188903 : List Nat := [1, 1, 5, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_8188903 : Nat := 118140960795 + 8188903 * 2 ^ 59
def prefixEnd_8188903 : Nat := 4983230072969 + 3 ^ 40 * 8188903 * 2
def baseEnd_8188903 : Nat := 4204843272045079613052427

theorem tailTrace_8188903 : CollatzResearch.WordTrace tailWord_8188903 prefixEnd_8188903 4204843272045079613052427 := by
  unfold tailWord_8188903
  simp only [CollatzResearch.WordTrace]
  refine ⟨298673829452010459132995363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199115886301340306088663575 298673829452010459132995363)
  ·
    refine ⟨448010744178015688699493045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298673829452010459132995363 448010744178015688699493045)
    ·
      refine ⟨42001007266688970815577473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 448010744178015688699493045 42001007266688970815577473)
      ·
        refine ⟨31500755450016728111683105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42001007266688970815577473 31500755450016728111683105)
        ·
          refine ⟨23625566587512546083762329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31500755450016728111683105 23625566587512546083762329)
          ·
            refine ⟨17719174940634409562821747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23625566587512546083762329 17719174940634409562821747)
            ·
              refine ⟨26578762410951614344232621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17719174940634409562821747 26578762410951614344232621)
              ·
                refine ⟨9967035904106855379087233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26578762410951614344232621 9967035904106855379087233)
                ·
                  refine ⟨7475276928080141534315425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9967035904106855379087233 7475276928080141534315425)
                  ·
                    refine ⟨5606457696060106150736569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7475276928080141534315425 5606457696060106150736569)
                    ·
                      refine ⟨4204843272045079613052427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606457696060106150736569 4204843272045079613052427)
                      ·
                        rfl

theorem cell23_8188903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_8188903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188903 prefixEnd_8188903 := by exact prefixLift 8188903
  have htrace : WordTrace (prefixWord ++ tailWord_8188903) baseStart_8188903 baseEnd_8188903 := by
    simpa [prefixWord, tailWord_8188903, baseEnd_8188903] using wordTrace_append hprefix tailTrace_8188903
  have hstable : (prefixWord ++ tailWord_8188903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188903).length < 2 ^ (prefixWord ++ tailWord_8188903).sum := by decide
  have hdescent : baseEnd_8188903 < baseStart_8188903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188959 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 1, 6, 2]
def baseStart_8188959 : Nat := 118140960795 + 8188959 * 2 ^ 59
def prefixEnd_8188959 : Nat := 4983230072969 + 3 ^ 40 * 8188959 * 2
def baseEnd_8188959 : Nat := 4204872026961731393952169

theorem tailTrace_8188959 : CollatzResearch.WordTrace tailWord_8188959 prefixEnd_8188959 4204872026961731393952169 := by
  unfold tailWord_8188959
  simp only [CollatzResearch.WordTrace]
  refine ⟨298675871939807580697033931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199117247959871720464689287 298675871939807580697033931)
  ·
    refine ⟨448013807909711371045550897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298675871939807580697033931 448013807909711371045550897)
    ·
      refine ⟨336010355932283528284163173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448013807909711371045550897 336010355932283528284163173)
      ·
        refine ⟨63001941737303161553280595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336010355932283528284163173 63001941737303161553280595)
        ·
          refine ⟨94502912605954742329920893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63001941737303161553280595 94502912605954742329920893)
          ·
            refine ⟨35438592227233028373720335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94502912605954742329920893 35438592227233028373720335)
            ·
              refine ⟨53157888340849542560580503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35438592227233028373720335 53157888340849542560580503)
              ·
                refine ⟨79736832511274313840870755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53157888340849542560580503 79736832511274313840870755)
                ·
                  refine ⟨119605248766911470761306133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79736832511274313840870755 119605248766911470761306133)
                  ·
                    refine ⟨5606496035948975191936225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119605248766911470761306133 5606496035948975191936225)
                    ·
                      refine ⟨4204872026961731393952169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606496035948975191936225 4204872026961731393952169)
                      ·
                        rfl

theorem cell23_8188959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_8188959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188959 prefixEnd_8188959 := by exact prefixLift 8188959
  have htrace : WordTrace (prefixWord ++ tailWord_8188959) baseStart_8188959 baseEnd_8188959 := by
    simpa [prefixWord, tailWord_8188959, baseEnd_8188959] using wordTrace_append hprefix tailTrace_8188959
  have hstable : (prefixWord ++ tailWord_8188959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188959).length < 2 ^ (prefixWord ++ tailWord_8188959).sum := by decide
  have hdescent : baseEnd_8188959 < baseStart_8188959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188986 : List Nat := [3, 1, 1, 1, 3, 1, 3, 5, 1, 4]
def baseStart_8188986 : Nat := 118140960795 + 8188986 * 2 ^ 59
def prefixEnd_8188986 : Nat := 4983230072969 + 3 ^ 40 * 8188986 * 2
def baseEnd_8188986 : Nat := 1401628630313134262771515

theorem tailTrace_8188986 : CollatzResearch.WordTrace tailWord_8188986 prefixEnd_8188986 1401628630313134262771515 := by
  unfold tailWord_8188986
  simp only [CollatzResearch.WordTrace]
  refine ⟨74669214177677441077066703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199117904473806509538844541 74669214177677441077066703)
  ·
    refine ⟨112003821266516161615600055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74669214177677441077066703 112003821266516161615600055)
    ·
      refine ⟨168005731899774242423400083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112003821266516161615600055 168005731899774242423400083)
      ·
        refine ⟨252008597849661363635100125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168005731899774242423400083 252008597849661363635100125)
        ·
          refine ⟨94503224193623011363162547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252008597849661363635100125 94503224193623011363162547)
          ·
            refine ⟨141754836290434517044743821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94503224193623011363162547 141754836290434517044743821)
            ·
              refine ⟨53158063608912943891778933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141754836290434517044743821 53158063608912943891778933)
              ·
                refine ⟨4983568463335588489854275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53158063608912943891778933 4983568463335588489854275)
                ·
                  refine ⟨7475352695003382734781413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4983568463335588489854275 7475352695003382734781413)
                  ·
                    refine ⟨1401628630313134262771515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7475352695003382734781413 1401628630313134262771515)
                    ·
                      rfl

theorem cell23_8188986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_8188986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188986 prefixEnd_8188986 := by exact prefixLift 8188986
  have htrace : WordTrace (prefixWord ++ tailWord_8188986) baseStart_8188986 baseEnd_8188986 := by
    simpa [prefixWord, tailWord_8188986, baseEnd_8188986] using wordTrace_append hprefix tailTrace_8188986
  have hstable : (prefixWord ++ tailWord_8188986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188986).length < 2 ^ (prefixWord ++ tailWord_8188986).sum := by decide
  have hdescent : baseEnd_8188986 < baseStart_8188986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8188999 : List Nat := [1, 1, 4, 1, 3, 2, 3, 2, 6]
def baseStart_8188999 : Nat := 118140960795 + 8188999 * 2 ^ 59
def prefixEnd_8188999 : Nat := 4983230072969 + 3 ^ 40 * 8188999 * 2
def baseEnd_8188999 : Nat := 467210285131990137494665

theorem tailTrace_8188999 : CollatzResearch.WordTrace tailWord_8188999 prefixEnd_8188999 467210285131990137494665 := by
  unfold tailWord_8188999
  simp only [CollatzResearch.WordTrace]
  refine ⟨298677330859662667528490051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199118220573108445018993367 298677330859662667528490051)
  ·
    refine ⟨448015996289494001292735077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298677330859662667528490051 448015996289494001292735077)
    ·
      refine ⟨84002999304280125242387827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448015996289494001292735077 84002999304280125242387827)
      ·
        refine ⟨126004498956420187863581741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84002999304280125242387827 126004498956420187863581741)
        ·
          refine ⟨47251687108657570448843153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126004498956420187863581741 47251687108657570448843153)
          ·
            refine ⟨35438765331493177836632365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47251687108657570448843153 35438765331493177836632365)
            ·
              refine ⟨13289536999309941688737137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35438765331493177836632365 13289536999309941688737137)
              ·
                refine ⟨9967152749482456266552853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13289536999309941688737137 9967152749482456266552853)
                ·
                  refine ⟨467210285131990137494665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9967152749482456266552853 467210285131990137494665)
                  ·
                    rfl

theorem cell23_8188999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 6].length) (baseStart_8188999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8188999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8188999 prefixEnd_8188999 := by exact prefixLift 8188999
  have htrace : WordTrace (prefixWord ++ tailWord_8188999) baseStart_8188999 baseEnd_8188999 := by
    simpa [prefixWord, tailWord_8188999, baseEnd_8188999] using wordTrace_append hprefix tailTrace_8188999
  have hstable : (prefixWord ++ tailWord_8188999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8188999).length < 2 ^ (prefixWord ++ tailWord_8188999).sum := by decide
  have hdescent : baseEnd_8188999 < baseStart_8188999 := by decide
  rcases family_descends (prefixWord ++ tailWord_8188999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189002 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_8189002 : Nat := 118140960795 + 8189002 * 2 ^ 59
def prefixEnd_8189002 : Nat := 4983230072969 + 3 ^ 40 * 8189002 * 2
def baseEnd_8189002 : Nat := 4204894106629874725714471

theorem tailTrace_8189002 : CollatzResearch.WordTrace tailWord_8189002 prefixEnd_8189002 4204894106629874725714471 := by
  unfold tailWord_8189002
  simp only [CollatzResearch.WordTrace]
  refine ⟨74669360069662949760212315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199118293519101199360566173 74669360069662949760212315)
  ·
    refine ⟨112004040104494424640318473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74669360069662949760212315 112004040104494424640318473)
    ·
      refine ⟨84003030078370818480238855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112004040104494424640318473 84003030078370818480238855)
      ·
        refine ⟨126004545117556227720358283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84003030078370818480238855 126004545117556227720358283)
        ·
          refine ⟨189006817676334341580537425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126004545117556227720358283 189006817676334341580537425)
          ·
            refine ⟨141755113257250756185403069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189006817676334341580537425 141755113257250756185403069)
            ·
              refine ⟨53158167471469033569526151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141755113257250756185403069 53158167471469033569526151)
              ·
                refine ⟨79737251207203550354289227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53158167471469033569526151 79737251207203550354289227)
                ·
                  refine ⟨119605876810805325531433841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79737251207203550354289227 119605876810805325531433841)
                  ·
                    refine ⟨89704407608103994148575381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119605876810805325531433841 89704407608103994148575381)
                    ·
                      refine ⟨4204894106629874725714471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89704407608103994148575381 4204894106629874725714471)
                      ·
                        rfl

theorem cell23_8189002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_8189002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189002 prefixEnd_8189002 := by exact prefixLift 8189002
  have htrace : WordTrace (prefixWord ++ tailWord_8189002) baseStart_8189002 baseEnd_8189002 := by
    simpa [prefixWord, tailWord_8189002, baseEnd_8189002] using wordTrace_append hprefix tailTrace_8189002
  have hstable : (prefixWord ++ tailWord_8189002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189002).length < 2 ^ (prefixWord ++ tailWord_8189002).sum := by decide
  have hdescent : baseEnd_8189002 < baseStart_8189002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189036 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 2, 3, 2]
def baseStart_8189036 : Nat := 118140960795 + 8189036 * 2 ^ 59
def prefixEnd_8189036 : Nat := 4983230072969 + 3 ^ 40 * 8189036 * 2
def baseEnd_8189036 : Nat := 4204911564972127592689315

theorem tailTrace_8189036 : CollatzResearch.WordTrace tailWord_8189036 prefixEnd_8189036 4204911564972127592689315 := by
  unfold tailWord_8189036
  simp only [CollatzResearch.WordTrace]
  refine ⟨149339340180264311423793481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199119120240352415231724641 149339340180264311423793481)
  ·
    refine ⟨112004505135198233567845111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149339340180264311423793481 112004505135198233567845111)
    ·
      refine ⟨168006757702797350351767667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112004505135198233567845111 168006757702797350351767667)
      ·
        refine ⟨252010136554196025527651501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168006757702797350351767667 252010136554196025527651501)
        ·
          refine ⟨94503801207823509572869313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252010136554196025527651501 94503801207823509572869313)
          ·
            refine ⟨70877850905867632179651985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94503801207823509572869313 70877850905867632179651985)
            ·
              refine ⟨53158388179400724134738989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70877850905867632179651985 53158388179400724134738989)
              ·
                refine ⟨19934395567275271550527121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53158388179400724134738989 19934395567275271550527121)
                ·
                  refine ⟨14950796675456453662895341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19934395567275271550527121 14950796675456453662895341)
                  ·
                    refine ⟨5606548753296170123585753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14950796675456453662895341 5606548753296170123585753)
                    ·
                      refine ⟨4204911564972127592689315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606548753296170123585753 4204911564972127592689315)
                      ·
                        rfl

theorem cell23_8189036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 3, 2].length) (baseStart_8189036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189036 prefixEnd_8189036 := by exact prefixLift 8189036
  have htrace : WordTrace (prefixWord ++ tailWord_8189036) baseStart_8189036 baseEnd_8189036 := by
    simpa [prefixWord, tailWord_8189036, baseEnd_8189036] using wordTrace_append hprefix tailTrace_8189036
  have hstable : (prefixWord ++ tailWord_8189036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189036).length < 2 ^ (prefixWord ++ tailWord_8189036).sum := by decide
  have hdescent : baseEnd_8189036 < baseStart_8189036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189046 : List Nat := [5, 1, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_8189046 : Nat := 118140960795 + 8189046 * 2 ^ 59
def prefixEnd_8189046 : Nat := 4983230072969 + 3 ^ 40 * 8189046 * 2
def baseEnd_8189046 : Nat := 1401638899926224184521423

theorem tailTrace_8189046 : CollatzResearch.WordTrace tailWord_8189046 prefixEnd_8189046 1401638899926224184521423 := by
  unfold tailWord_8189046
  simp only [CollatzResearch.WordTrace]
  refine ⟨18667440318155774659715687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199119363393661596370300661 18667440318155774659715687)
  ·
    refine ⟨28001160477233661989573531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18667440318155774659715687 28001160477233661989573531)
    ·
      refine ⟨42001740715850492984360297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28001160477233661989573531 42001740715850492984360297)
      ·
        refine ⟨31501305536887869738270223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42001740715850492984360297 31501305536887869738270223)
        ·
          refine ⟨47251958305331804607405335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31501305536887869738270223 47251958305331804607405335)
          ·
            refine ⟨70877937457997706911108003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47251958305331804607405335 70877937457997706911108003)
            ·
              refine ⟨106316906186996560366662005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70877937457997706911108003 106316906186996560366662005)
              ·
                refine ⟨9967209955030927534374563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106316906186996560366662005 9967209955030927534374563)
                ·
                  refine ⟨14950814932546391301561845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9967209955030927534374563 14950814932546391301561845)
                  ·
                    refine ⟨1401638899926224184521423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14950814932546391301561845 1401638899926224184521423)
                    ·
                      rfl

theorem cell23_8189046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_8189046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189046 prefixEnd_8189046 := by exact prefixLift 8189046
  have htrace : WordTrace (prefixWord ++ tailWord_8189046) baseStart_8189046 baseEnd_8189046 := by
    simpa [prefixWord, tailWord_8189046, baseEnd_8189046] using wordTrace_append hprefix tailTrace_8189046
  have hstable : (prefixWord ++ tailWord_8189046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189046).length < 2 ^ (prefixWord ++ tailWord_8189046).sum := by decide
  have hdescent : baseEnd_8189046 < baseStart_8189046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189054 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_8189054 : Nat := 118140960795 + 8189054 * 2 ^ 59
def prefixEnd_8189054 : Nat := 4983230072969 + 3 ^ 40 * 8189054 * 2
def baseEnd_8189054 : Nat := 1401640269207969507421411

theorem tailTrace_8189054 : CollatzResearch.WordTrace tailWord_8189054 prefixEnd_8189054 1401640269207969507421411 := by
  unfold tailWord_8189054
  simp only [CollatzResearch.WordTrace]
  refine ⟨37334917109307926490217777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199119557916308941281161477 37334917109307926490217777)
  ·
    refine ⟨28001187831980944867663333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37334917109307926490217777 28001187831980944867663333)
    ·
      refine ⟨5250222718496427162686875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28001187831980944867663333 5250222718496427162686875)
      ·
        refine ⟨7875334077744640744030313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250222718496427162686875 7875334077744640744030313)
        ·
          refine ⟨5906500558308480558022735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7875334077744640744030313 5906500558308480558022735)
          ·
            refine ⟨8859750837462720837034103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5906500558308480558022735 8859750837462720837034103)
            ·
              refine ⟨13289626256194081255551155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8859750837462720837034103 13289626256194081255551155)
              ·
                refine ⟨19934439384291121883326733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13289626256194081255551155 19934439384291121883326733)
                ·
                  refine ⟨7475414769109170706247525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19934439384291121883326733 7475414769109170706247525)
                  ·
                    refine ⟨1401640269207969507421411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7475414769109170706247525 1401640269207969507421411)
                    ·
                      rfl

theorem cell23_8189054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_8189054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189054 prefixEnd_8189054 := by exact prefixLift 8189054
  have htrace : WordTrace (prefixWord ++ tailWord_8189054) baseStart_8189054 baseEnd_8189054 := by
    simpa [prefixWord, tailWord_8189054, baseEnd_8189054] using wordTrace_append hprefix tailTrace_8189054
  have hstable : (prefixWord ++ tailWord_8189054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189054).length < 2 ^ (prefixWord ++ tailWord_8189054).sum := by decide
  have hdescent : baseEnd_8189054 < baseStart_8189054 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189059 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 4, 4]
def baseStart_8189059 : Nat := 118140960795 + 8189059 * 2 ^ 59
def prefixEnd_8189059 : Nat := 4983230072969 + 3 ^ 40 * 8189059 * 2
def baseEnd_8189059 : Nat := 1401641125009060334233903

theorem tailTrace_8189059 : CollatzResearch.WordTrace tailWord_8189059 prefixEnd_8189059 1401641125009060334233903 := by
  unfold tailWord_8189059
  simp only [CollatzResearch.WordTrace]
  refine ⟨298679519239445297775674231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199119679492963531850449487 298679519239445297775674231)
  ·
    refine ⟨448019278859167946663511347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298679519239445297775674231 448019278859167946663511347)
    ·
      refine ⟨672028918288751919995267021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448019278859167946663511347 672028918288751919995267021)
      ·
        refine ⟨252010844358281969998225133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 672028918288751919995267021 252010844358281969998225133)
        ·
          refine ⟨94504066634355738749334425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252010844358281969998225133 94504066634355738749334425)
          ·
            refine ⟨70878049975766804062000819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94504066634355738749334425 70878049975766804062000819)
            ·
              refine ⟨106317074963650206093001229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70878049975766804062000819 106317074963650206093001229)
              ·
                refine ⟨39868903111368827284875461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106317074963650206093001229 39868903111368827284875461)
                ·
                  refine ⟨7475419333381655115914149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39868903111368827284875461 7475419333381655115914149)
                  ·
                    refine ⟨1401641125009060334233903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7475419333381655115914149 1401641125009060334233903)
                    ·
                      rfl

theorem cell23_8189059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 4].length) (baseStart_8189059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189059 prefixEnd_8189059 := by exact prefixLift 8189059
  have htrace : WordTrace (prefixWord ++ tailWord_8189059) baseStart_8189059 baseEnd_8189059 := by
    simpa [prefixWord, tailWord_8189059, baseEnd_8189059] using wordTrace_append hprefix tailTrace_8189059
  have hstable : (prefixWord ++ tailWord_8189059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189059).length < 2 ^ (prefixWord ++ tailWord_8189059).sum := by decide
  have hdescent : baseEnd_8189059 < baseStart_8189059 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189079 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 6]
def baseStart_8189079 : Nat := 118140960795 + 8189079 * 2 ^ 59
def prefixEnd_8189079 : Nat := 4983230072969 + 3 ^ 40 * 8189079 * 2
def baseEnd_8189079 : Nat := 4204933644640270924451617

theorem tailTrace_8189079 : CollatzResearch.WordTrace tailWord_8189079 prefixEnd_8189079 4204933644640270924451617 := by
  unfold tailWord_8189079
  simp only [CollatzResearch.WordTrace]
  refine ⟨298680248699372841191402291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199120165799581894127601527 298680248699372841191402291)
  ·
    refine ⟨448020373049059261787103437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298680248699372841191402291 448020373049059261787103437)
    ·
      refine ⟨168007639893397223170163789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448020373049059261787103437 168007639893397223170163789)
      ·
        refine ⟨63002864960023958688811421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168007639893397223170163789 63002864960023958688811421)
        ·
          refine ⟨23626074360008984508304283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63002864960023958688811421 23626074360008984508304283)
          ·
            refine ⟨35439111540013476762456425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23626074360008984508304283 35439111540013476762456425)
            ·
              refine ⟨26579333655010107571842319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35439111540013476762456425 26579333655010107571842319)
              ·
                refine ⟨39869000482515161357763479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26579333655010107571842319 39869000482515161357763479)
                ·
                  refine ⟨59803500723772742036645219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39869000482515161357763479 59803500723772742036645219)
                  ·
                    refine ⟨89705251085659113054967829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59803500723772742036645219 89705251085659113054967829)
                    ·
                      refine ⟨4204933644640270924451617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89705251085659113054967829 4204933644640270924451617)
                      ·
                        rfl

theorem cell23_8189079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_8189079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189079 prefixEnd_8189079 := by exact prefixLift 8189079
  have htrace : WordTrace (prefixWord ++ tailWord_8189079) baseStart_8189079 baseEnd_8189079 := by
    simpa [prefixWord, tailWord_8189079, baseEnd_8189079] using wordTrace_append hprefix tailTrace_8189079
  have hstable : (prefixWord ++ tailWord_8189079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189079).length < 2 ^ (prefixWord ++ tailWord_8189079).sum := by decide
  have hdescent : baseEnd_8189079 < baseStart_8189079 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189117 : List Nat := [1, 4, 1, 2, 1, 1, 6, 2, 1, 2, 2]
def baseStart_8189117 : Nat := 118140960795 + 8189117 * 2 ^ 59
def prefixEnd_8189117 : Nat := 4983230072969 + 3 ^ 40 * 8189117 * 2
def baseEnd_8189117 : Nat := 4204953156905141775776443

theorem tailTrace_8189117 : CollatzResearch.WordTrace tailWord_8189117 prefixEnd_8189117 4204953156905141775776443 := by
  unfold tailWord_8189117
  simp only [CollatzResearch.WordTrace]
  refine ⟨298681634673235173681285605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199121089782156782454190403 298681634673235173681285605)
  ·
    refine ⟨56002806501231595065241051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298681634673235173681285605 56002806501231595065241051)
    ·
      refine ⟨84004209751847392597861577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56002806501231595065241051 84004209751847392597861577)
      ·
        refine ⟨63003157313885544448396183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84004209751847392597861577 63003157313885544448396183)
        ·
          refine ⟨94504735970828316672594275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63003157313885544448396183 94504735970828316672594275)
          ·
            refine ⟨141757103956242475008891413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94504735970828316672594275 141757103956242475008891413)
            ·
              refine ⟨6644864247948866016041785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141757103956242475008891413 6644864247948866016041785)
              ·
                refine ⟨4983648185961649512031339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6644864247948866016041785 4983648185961649512031339)
                ·
                  refine ⟨7475472278942474268047009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4983648185961649512031339 7475472278942474268047009)
                  ·
                    refine ⟨5606604209206855701035257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7475472278942474268047009 5606604209206855701035257)
                    ·
                      refine ⟨4204953156905141775776443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606604209206855701035257 4204953156905141775776443)
                      ·
                        rfl

theorem cell23_8189117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_8189117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189117 prefixEnd_8189117 := by exact prefixLift 8189117
  have htrace : WordTrace (prefixWord ++ tailWord_8189117) baseStart_8189117 baseEnd_8189117 := by
    simpa [prefixWord, tailWord_8189117, baseEnd_8189117] using wordTrace_append hprefix tailTrace_8189117
  have hstable : (prefixWord ++ tailWord_8189117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189117).length < 2 ^ (prefixWord ++ tailWord_8189117).sum := by decide
  have hdescent : baseEnd_8189117 < baseStart_8189117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189167 : List Nat := [1, 1, 2, 1, 8, 1, 1, 2, 2, 1, 3]
def baseStart_8189167 : Nat := 118140960795 + 8189167 * 2 ^ 59
def prefixEnd_8189167 : Nat := 4983230072969 + 3 ^ 40 * 8189167 * 2
def baseEnd_8189167 : Nat := 4204978830937866580151213

theorem tailTrace_8189167 : CollatzResearch.WordTrace tailWord_8189167 prefixEnd_8189167 4204978830937866580151213 := by
  unfold tailWord_8189167
  simp only [CollatzResearch.WordTrace]
  refine ⟨298683458323054032220605755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199122305548702688147070503 298683458323054032220605755)
  ·
    refine ⟨448025187484581048330908633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298683458323054032220605755 448025187484581048330908633)
    ·
      refine ⟨336018890613435786248181475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448025187484581048330908633 336018890613435786248181475)
      ·
        refine ⟨504028335920153679372272213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336018890613435786248181475 504028335920153679372272213)
        ·
          refine ⟨5906582061564300930143815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 504028335920153679372272213 5906582061564300930143815)
          ·
            refine ⟨8859873092346451395215723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5906582061564300930143815 8859873092346451395215723)
            ·
              refine ⟨13289809638519677092823585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8859873092346451395215723 13289809638519677092823585)
              ·
                refine ⟨9967357228889757819617689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13289809638519677092823585 9967357228889757819617689)
                ·
                  refine ⟨7475517921667318364713267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9967357228889757819617689 7475517921667318364713267)
                  ·
                    refine ⟨11213276882500977547069901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7475517921667318364713267 11213276882500977547069901)
                    ·
                      refine ⟨4204978830937866580151213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11213276882500977547069901 4204978830937866580151213)
                      ·
                        rfl

theorem cell23_8189167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 2, 1, 3].length) (baseStart_8189167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189167 prefixEnd_8189167 := by exact prefixLift 8189167
  have htrace : WordTrace (prefixWord ++ tailWord_8189167) baseStart_8189167 baseEnd_8189167 := by
    simpa [prefixWord, tailWord_8189167, baseEnd_8189167] using wordTrace_append hprefix tailTrace_8189167
  have hstable : (prefixWord ++ tailWord_8189167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189167).length < 2 ^ (prefixWord ++ tailWord_8189167).sum := by decide
  have hdescent : baseEnd_8189167 < baseStart_8189167 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189209 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 8, 5]
def baseStart_8189209 : Nat := 118140960795 + 8189209 * 2 ^ 59
def prefixEnd_8189209 : Nat := 4983230072969 + 3 ^ 40 * 8189209 * 2
def baseEnd_8189209 : Nat := 1401666799041785138608673

theorem tailTrace_8189209 : CollatzResearch.WordTrace tailWord_8189209 prefixEnd_8189209 1401666799041785138608673 := by
  unfold tailWord_8189209
  simp only [CollatzResearch.WordTrace]
  refine ⟨298684990188901873393634681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199123326792601248929089787 298684990188901873393634681)
  ·
    refine ⟨224013742641676405045226011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298684990188901873393634681 224013742641676405045226011)
    ·
      refine ⟨336020613962514607567839017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224013742641676405045226011 336020613962514607567839017)
      ·
        refine ⟨252015460471885955675879263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336020613962514607567839017 252015460471885955675879263)
        ·
          refine ⟨378023190707828933513818895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252015460471885955675879263 378023190707828933513818895)
          ·
            refine ⟨567034786061743400270728343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378023190707828933513818895 567034786061743400270728343)
            ·
              refine ⟨850552179092615100406092515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567034786061743400270728343 850552179092615100406092515)
              ·
                refine ⟨1275828268638922650609138773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850552179092615100406092515 1275828268638922650609138773)
                ·
                  refine ⟨14951112523112374811825845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1275828268638922650609138773 14951112523112374811825845)
                  ·
                    refine ⟨1401666799041785138608673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14951112523112374811825845 1401666799041785138608673)
                    ·
                      rfl

theorem cell23_8189209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 5].length) (baseStart_8189209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189209 prefixEnd_8189209 := by exact prefixLift 8189209
  have htrace : WordTrace (prefixWord ++ tailWord_8189209) baseStart_8189209 baseEnd_8189209 := by
    simpa [prefixWord, tailWord_8189209, baseEnd_8189209] using wordTrace_append hprefix tailTrace_8189209
  have hstable : (prefixWord ++ tailWord_8189209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189209).length < 2 ^ (prefixWord ++ tailWord_8189209).sum := by decide
  have hdescent : baseEnd_8189209 < baseStart_8189209 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189241 : List Nat := [1, 2, 1, 6, 3, 1, 2, 1, 2, 2, 2]
def baseStart_8189241 : Nat := 118140960795 + 8189241 * 2 ^ 59
def prefixEnd_8189241 : Nat := 4983230072969 + 3 ^ 40 * 8189241 * 2
def baseEnd_8189241 : Nat := 4205016828506299290625873

theorem tailTrace_8189241 : CollatzResearch.WordTrace tailWord_8189241 prefixEnd_8189241 4205016828506299290625873 := by
  unfold tailWord_8189241
  simp only [CollatzResearch.WordTrace]
  refine ⟨298686157324785942858799577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199124104883190628572533051 298686157324785942858799577)
  ·
    refine ⟨224014617993589457144099683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298686157324785942858799577 224014617993589457144099683)
    ·
      refine ⟨336021926990384185716149525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224014617993589457144099683 336021926990384185716149525)
      ·
        refine ⟨15751027827674258705444509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 336021926990384185716149525 15751027827674258705444509)
        ·
          refine ⟨5906635435377847014541691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15751027827674258705444509 5906635435377847014541691)
          ·
            refine ⟨8859953153066770521812537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5906635435377847014541691 8859953153066770521812537)
            ·
              refine ⟨6644964864800077891359403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8859953153066770521812537 6644964864800077891359403)
              ·
                refine ⟨9967447297200116837039105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6644964864800077891359403 9967447297200116837039105)
                ·
                  refine ⟨7475585472900087627779329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9967447297200116837039105 7475585472900087627779329)
                  ·
                    refine ⟨5606689104675065720834497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7475585472900087627779329 5606689104675065720834497)
                    ·
                      refine ⟨4205016828506299290625873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606689104675065720834497 4205016828506299290625873)
                      ·
                        rfl

theorem cell23_8189241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_8189241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189241 prefixEnd_8189241 := by exact prefixLift 8189241
  have htrace : WordTrace (prefixWord ++ tailWord_8189241) baseStart_8189241 baseEnd_8189241 := by
    simpa [prefixWord, tailWord_8189241, baseEnd_8189241] using wordTrace_append hprefix tailTrace_8189241
  have hstable : (prefixWord ++ tailWord_8189241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189241).length < 2 ^ (prefixWord ++ tailWord_8189241).sum := by decide
  have hdescent : baseEnd_8189241 < baseStart_8189241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189256 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 5, 4]
def baseStart_8189256 : Nat := 118140960795 + 8189256 * 2 ^ 59
def prefixEnd_8189256 : Nat := 4983230072969 + 3 ^ 40 * 8189256 * 2
def baseEnd_8189256 : Nat := 1401674843572038910646101

theorem tailTrace_8189256 : CollatzResearch.WordTrace tailWord_8189256 prefixEnd_8189256 1401674843572038910646101 := by
  unfold tailWord_8189256
  simp only [CollatzResearch.WordTrace]
  refine ⟨149343352209865800210297811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199124469613154400280397081 149343352209865800210297811)
  ·
    refine ⟨224015028314798700315446717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149343352209865800210297811 224015028314798700315446717)
    ·
      refine ⟨84005635618049512618292519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224015028314798700315446717 84005635618049512618292519)
      ·
        refine ⟨126008453427074268927438779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84005635618049512618292519 126008453427074268927438779)
        ·
          refine ⟨189012680140611403391158169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126008453427074268927438779 189012680140611403391158169)
          ·
            refine ⟨141759510105458552543368627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189012680140611403391158169 141759510105458552543368627)
            ·
              refine ⟨212639265158187828815052941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141759510105458552543368627 212639265158187828815052941)
              ·
                refine ⟨79739724434320435805644853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212639265158187828815052941 79739724434320435805644853)
                ·
                  refine ⟨7475599165717540856779205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79739724434320435805644853 7475599165717540856779205)
                  ·
                    refine ⟨1401674843572038910646101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7475599165717540856779205 1401674843572038910646101)
                    ·
                      rfl

theorem cell23_8189256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_8189256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189256 prefixEnd_8189256 := by exact prefixLift 8189256
  have htrace : WordTrace (prefixWord ++ tailWord_8189256) baseStart_8189256 baseEnd_8189256 := by
    simpa [prefixWord, tailWord_8189256, baseEnd_8189256] using wordTrace_append hprefix tailTrace_8189256
  have hstable : (prefixWord ++ tailWord_8189256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189256).length < 2 ^ (prefixWord ++ tailWord_8189256).sum := by decide
  have hdescent : baseEnd_8189256 < baseStart_8189256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189283 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 3]
def baseStart_8189283 : Nat := 118140960795 + 8189283 * 2 ^ 59
def prefixEnd_8189283 : Nat := 4983230072969 + 3 ^ 40 * 8189283 * 2
def baseEnd_8189283 : Nat := 4205038394693788126300679

theorem tailTrace_8189283 : CollatzResearch.WordTrace tailWord_8189283 prefixEnd_8189283 4205038394693788126300679 := by
  unfold tailWord_8189283
  simp only [CollatzResearch.WordTrace]
  refine ⟨298687689190633784031828503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199125126127089189354552335 298687689190633784031828503)
  ·
    refine ⟨448031533785950676047742755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298687689190633784031828503 448031533785950676047742755)
    ·
      refine ⟨672047300678926014071614133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448031533785950676047742755 672047300678926014071614133)
      ·
        refine ⟨63004434438649313819213825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 672047300678926014071614133 63004434438649313819213825)
        ·
          refine ⟨47253325828986985364410369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63004434438649313819213825 47253325828986985364410369)
          ·
            refine ⟨35439994371740239023307777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47253325828986985364410369 35439994371740239023307777)
            ·
              refine ⟨26579995778805179267480833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35439994371740239023307777 26579995778805179267480833)
              ·
                refine ⟨19934996834103884450610625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26579995778805179267480833 19934996834103884450610625)
                ·
                  refine ⟨14951247625577913337957969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19934996834103884450610625 14951247625577913337957969)
                  ·
                    refine ⟨11213435719183435003468477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14951247625577913337957969 11213435719183435003468477)
                    ·
                      refine ⟨4205038394693788126300679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11213435719183435003468477 4205038394693788126300679)
                      ·
                        rfl

theorem cell23_8189283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_8189283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189283 prefixEnd_8189283 := by exact prefixLift 8189283
  have htrace : WordTrace (prefixWord ++ tailWord_8189283) baseStart_8189283 baseEnd_8189283 := by
    simpa [prefixWord, tailWord_8189283, baseEnd_8189283] using wordTrace_append hprefix tailTrace_8189283
  have hstable : (prefixWord ++ tailWord_8189283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189283).length < 2 ^ (prefixWord ++ tailWord_8189283).sum := by decide
  have hdescent : baseEnd_8189283 < baseStart_8189283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189299 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 1, 11]
def baseStart_8189299 : Nat := 118140960795 + 8189299 * 2 ^ 59
def prefixEnd_8189299 : Nat := 4983230072969 + 3 ^ 40 * 8189299 * 2
def baseEnd_8189299 : Nat := 1401682203461420021233535

theorem tailTrace_8189299 : CollatzResearch.WordTrace tailWord_8189299 prefixEnd_8189299 1401682203461420021233535 := by
  unfold tailWord_8189299
  simp only [CollatzResearch.WordTrace]
  refine ⟨298688272758575818764410951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199125515172383879176273967 298688272758575818764410951)
  ·
    refine ⟨448032409137863728146616427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298688272758575818764410951 448032409137863728146616427)
    ·
      refine ⟨672048613706795592219924641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448032409137863728146616427 672048613706795592219924641)
      ·
        refine ⟨504036460280096694164943481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672048613706795592219924641 504036460280096694164943481)
        ·
          refine ⟨378027345210072520623707611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504036460280096694164943481 378027345210072520623707611)
          ·
            refine ⟨567041017815108780935561417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378027345210072520623707611 567041017815108780935561417)
            ·
              refine ⟨425280763361331585701671063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567041017815108780935561417 425280763361331585701671063)
              ·
                refine ⟨637921145041997378552506595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425280763361331585701671063 637921145041997378552506595)
                ·
                  refine ⟨956881717562996067828759893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637921145041997378552506595 956881717562996067828759893)
                  ·
                    refine ⟨1401682203461420021233535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 956881717562996067828759893 1401682203461420021233535)
                    ·
                      rfl

theorem cell23_8189299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 11].length) (baseStart_8189299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189299 prefixEnd_8189299 := by exact prefixLift 8189299
  have htrace : WordTrace (prefixWord ++ tailWord_8189299) baseStart_8189299 baseEnd_8189299 := by
    simpa [prefixWord, tailWord_8189299, baseEnd_8189299] using wordTrace_append hprefix tailTrace_8189299
  have hstable : (prefixWord ++ tailWord_8189299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189299).length < 2 ^ (prefixWord ++ tailWord_8189299).sum := by decide
  have hdescent : baseEnd_8189299 < baseStart_8189299 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189323 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 1, 5, 2]
def baseStart_8189323 : Nat := 118140960795 + 8189323 * 2 ^ 59
def prefixEnd_8189323 : Nat := 4983230072969 + 3 ^ 40 * 8189323 * 2
def baseEnd_8189323 : Nat := 4205058933919967969800495

theorem tailTrace_8189323 : CollatzResearch.WordTrace tailWord_8189323 prefixEnd_8189323 4205058933919967969800495 := by
  unfold tailWord_8189323
  simp only [CollatzResearch.WordTrace]
  refine ⟨298689148110488870863284623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199126098740325913908856415 298689148110488870863284623)
  ·
    refine ⟨448033722165733306294926935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298689148110488870863284623 448033722165733306294926935)
    ·
      refine ⟨672050583248599959442390403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448033722165733306294926935 672050583248599959442390403)
      ·
        refine ⟨1008075874872899939163585605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672050583248599959442390403 1008075874872899939163585605)
        ·
          refine ⟨189014226538668738593172301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1008075874872899939163585605 189014226538668738593172301)
          ·
            refine ⟨70880334952000776972439613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189014226538668738593172301 70880334952000776972439613)
            ·
              refine ⟨26580125607000291364664855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70880334952000776972439613 26580125607000291364664855)
              ·
                refine ⟨39870188410500437046997283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26580125607000291364664855 39870188410500437046997283)
                ·
                  refine ⟨59805282615750655570495925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39870188410500437046997283 59805282615750655570495925)
                  ·
                    refine ⟨5606745245226623959733993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59805282615750655570495925 5606745245226623959733993)
                    ·
                      refine ⟨4205058933919967969800495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606745245226623959733993 4205058933919967969800495)
                      ·
                        rfl

theorem cell23_8189323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 5, 2].length) (baseStart_8189323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189323 prefixEnd_8189323 := by exact prefixLift 8189323
  have htrace : WordTrace (prefixWord ++ tailWord_8189323) baseStart_8189323 baseEnd_8189323 := by
    simpa [prefixWord, tailWord_8189323, baseEnd_8189323] using wordTrace_append hprefix tailTrace_8189323
  have hstable : (prefixWord ++ tailWord_8189323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189323).length < 2 ^ (prefixWord ++ tailWord_8189323).sum := by decide
  have hdescent : baseEnd_8189323 < baseStart_8189323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189356 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_8189356 : Nat := 118140960795 + 8189356 * 2 ^ 59
def prefixEnd_8189356 : Nat := 4983230072969 + 3 ^ 40 * 8189356 * 2
def baseEnd_8189356 : Nat := 4205075878781566340687843

theorem tailTrace_8189356 : CollatzResearch.WordTrace tailWord_8189356 prefixEnd_8189356 4205075878781566340687843 := by
  unfold tailWord_8189356
  simp only [CollatzResearch.WordTrace]
  refine ⟨149345175859684658749617961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199126901146246211666157281 149345175859684658749617961)
  ·
    refine ⟨112008881894763494062213471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149345175859684658749617961 112008881894763494062213471)
    ·
      refine ⟨168013322842145241093320207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112008881894763494062213471 168013322842145241093320207)
      ·
        refine ⟨252019984263217861639980311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168013322842145241093320207 252019984263217861639980311)
        ·
          refine ⟨378029976394826792459970467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252019984263217861639980311 378029976394826792459970467)
          ·
            refine ⟨567044964592240188689955701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378029976394826792459970467 567044964592240188689955701)
            ·
              refine ⟨53160465430522517689683347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 567044964592240188689955701 53160465430522517689683347)
              ·
                refine ⟨79740698145783776534525021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53160465430522517689683347 79740698145783776534525021)
                ·
                  refine ⟨29902761804668916200446883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79740698145783776534525021 29902761804668916200446883)
                  ·
                    refine ⟨44854142707003374300670325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29902761804668916200446883 44854142707003374300670325)
                    ·
                      refine ⟨4205075878781566340687843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44854142707003374300670325 4205075878781566340687843)
                      ·
                        rfl

theorem cell23_8189356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_8189356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189356 prefixEnd_8189356 := by exact prefixLift 8189356
  have htrace : WordTrace (prefixWord ++ tailWord_8189356) baseStart_8189356 baseEnd_8189356 := by
    simpa [prefixWord, tailWord_8189356, baseEnd_8189356] using wordTrace_append hprefix tailTrace_8189356
  have hstable : (prefixWord ++ tailWord_8189356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189356).length < 2 ^ (prefixWord ++ tailWord_8189356).sum := by decide
  have hdescent : baseEnd_8189356 < baseStart_8189356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189363 : List Nat := [1, 1, 1, 2, 3, 1, 1, 7, 2, 4]
def baseStart_8189363 : Nat := 118140960795 + 8189363 * 2 ^ 59
def prefixEnd_8189363 : Nat := 4983230072969 + 3 ^ 40 * 8189363 * 2
def baseEnd_8189363 : Nat := 1401693157715382604433437

theorem tailTrace_8189363 : CollatzResearch.WordTrace tailWord_8189363 prefixEnd_8189363 1401693157715382604433437 := by
  unfold tailWord_8189363
  simp only [CollatzResearch.WordTrace]
  refine ⟨298690607030343957694740743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199127071353562638463160495 298690607030343957694740743)
  ·
    refine ⟨448035910545515936542111115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298690607030343957694740743 448035910545515936542111115)
    ·
      refine ⟨672053865818273904813166673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448035910545515936542111115 672053865818273904813166673)
      ·
        refine ⟨504040399363705428609875005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672053865818273904813166673 504040399363705428609875005)
        ·
          refine ⟨189015149761389535728703127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504040399363705428609875005 189015149761389535728703127)
          ·
            refine ⟨283522724642084303593054691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189015149761389535728703127 283522724642084303593054691)
            ·
              refine ⟨425284086963126455389582037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283522724642084303593054691 425284086963126455389582037)
              ·
                refine ⟨9967595788198276298193329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 425284086963126455389582037 9967595788198276298193329)
                ·
                  refine ⟨7475696841148707223644997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9967595788198276298193329 7475696841148707223644997)
                  ·
                    refine ⟨1401693157715382604433437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7475696841148707223644997 1401693157715382604433437)
                    ·
                      rfl

theorem cell23_8189363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 4].length) (baseStart_8189363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189363 prefixEnd_8189363 := by exact prefixLift 8189363
  have htrace : WordTrace (prefixWord ++ tailWord_8189363) baseStart_8189363 baseEnd_8189363 := by
    simpa [prefixWord, tailWord_8189363, baseEnd_8189363] using wordTrace_append hprefix tailTrace_8189363
  have hstable : (prefixWord ++ tailWord_8189363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189363).length < 2 ^ (prefixWord ++ tailWord_8189363).sum := by decide
  have hdescent : baseEnd_8189363 < baseStart_8189363 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189380 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_8189380 : Nat := 118140960795 + 8189380 * 2 ^ 59
def prefixEnd_8189380 : Nat := 4983230072969 + 3 ^ 40 * 8189380 * 2
def baseEnd_8189380 : Nat := 1401696067439091415595911

theorem tailTrace_8189380 : CollatzResearch.WordTrace tailWord_8189380 prefixEnd_8189380 1401696067439091415595911 := by
  unfold tailWord_8189380
  simp only [CollatzResearch.WordTrace]
  refine ⟨149345613535641184799054797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199127484714188246398739729 149345613535641184799054797)
  ·
    refine ⟨56004605075865444299645549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149345613535641184799054797 56004605075865444299645549)
    ·
      refine ⟨21001726903449541612367081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56004605075865444299645549 21001726903449541612367081)
      ·
        refine ⟨15751295177587156209275311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21001726903449541612367081 15751295177587156209275311)
        ·
          refine ⟨23626942766380734313912967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15751295177587156209275311 23626942766380734313912967)
          ·
            refine ⟨35440414149571101470869451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23626942766380734313912967 35440414149571101470869451)
            ·
              refine ⟨53160621224356652206304177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35440414149571101470869451 53160621224356652206304177)
              ·
                refine ⟨39870465918267489154728133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53160621224356652206304177 39870465918267489154728133)
                ·
                  refine ⟨7475712359675154216511525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39870465918267489154728133 7475712359675154216511525)
                  ·
                    refine ⟨1401696067439091415595911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7475712359675154216511525 1401696067439091415595911)
                    ·
                      rfl

theorem cell23_8189380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_8189380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189380 prefixEnd_8189380 := by exact prefixLift 8189380
  have htrace : WordTrace (prefixWord ++ tailWord_8189380) baseStart_8189380 baseEnd_8189380 := by
    simpa [prefixWord, tailWord_8189380, baseEnd_8189380] using wordTrace_append hprefix tailTrace_8189380
  have hstable : (prefixWord ++ tailWord_8189380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189380).length < 2 ^ (prefixWord ++ tailWord_8189380).sum := by decide
  have hdescent : baseEnd_8189380 < baseStart_8189380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189390 : List Nat := [4, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_8189390 : Nat := 118140960795 + 8189390 * 2 ^ 59
def prefixEnd_8189390 : Nat := 4983230072969 + 3 ^ 40 * 8189390 * 2
def baseEnd_8189390 : Nat := 4205093337123819207662687

theorem tailTrace_8189390 : CollatzResearch.WordTrace tailWord_8189390 prefixEnd_8189390 4205093337123819207662687 := by
  unfold tailWord_8189390
  simp only [CollatzResearch.WordTrace]
  refine ⟨37336448975155767663246703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199127727867497427537315749 37336448975155767663246703)
  ·
    refine ⟨56004673462733651494870055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37336448975155767663246703 56004673462733651494870055)
    ·
      refine ⟨84007010194100477242305083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56004673462733651494870055 84007010194100477242305083)
      ·
        refine ⟨126010515291150715863457625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84007010194100477242305083 126010515291150715863457625)
        ·
          refine ⟨94507886468363036897593219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126010515291150715863457625 94507886468363036897593219)
          ·
            refine ⟨141761829702544555346389829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94507886468363036897593219 141761829702544555346389829)
            ·
              refine ⟨26580343069227104127448093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141761829702544555346389829 26580343069227104127448093)
              ·
                refine ⟨9967628650960164047793035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26580343069227104127448093 9967628650960164047793035)
                ·
                  refine ⟨14951442976440246071689553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9967628650960164047793035 14951442976440246071689553)
                  ·
                    refine ⟨11213582232330184553767165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14951442976440246071689553 11213582232330184553767165)
                    ·
                      refine ⟨4205093337123819207662687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11213582232330184553767165 4205093337123819207662687)
                      ·
                        rfl

theorem cell23_8189390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_8189390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189390 prefixEnd_8189390 := by exact prefixLift 8189390
  have htrace : WordTrace (prefixWord ++ tailWord_8189390) baseStart_8189390 baseEnd_8189390 := by
    simpa [prefixWord, tailWord_8189390, baseEnd_8189390] using wordTrace_append hprefix tailTrace_8189390
  have hstable : (prefixWord ++ tailWord_8189390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189390).length < 2 ^ (prefixWord ++ tailWord_8189390).sum := by decide
  have hdescent : baseEnd_8189390 < baseStart_8189390 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189454 : List Nat := [4, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_8189454 : Nat := 118140960795 + 8189454 * 2 ^ 59
def prefixEnd_8189454 : Nat := 4983230072969 + 3 ^ 40 * 8189454 * 2
def baseEnd_8189454 : Nat := 4205126199885706957262393

theorem tailTrace_8189454 : CollatzResearch.WordTrace tailWord_8189454 prefixEnd_8189454 4205126199885706957262393 := by
  unfold tailWord_8189454
  simp only [CollatzResearch.WordTrace]
  refine ⟨37336740759126785029537927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199129284048676186824202277 37336740759126785029537927)
  ·
    refine ⟨56005111138690177544306891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37336740759126785029537927 56005111138690177544306891)
    ·
      refine ⟨84007666708035266316460337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56005111138690177544306891 84007666708035266316460337)
      ·
        refine ⟨63005750031026449737345253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84007666708035266316460337 63005750031026449737345253)
        ·
          refine ⟨11813578130817459325752235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63005750031026449737345253 11813578130817459325752235)
          ·
            refine ⟨17720367196226188988628353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11813578130817459325752235 17720367196226188988628353)
            ·
              refine ⟨13290275397169641741471265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17720367196226188988628353 13290275397169641741471265)
              ·
                refine ⟨9967706547877231306103449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13290275397169641741471265 9967706547877231306103449)
                ·
                  refine ⟨7475779910907923479577587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9967706547877231306103449 7475779910907923479577587)
                  ·
                    refine ⟨11213669866361885219366381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7475779910907923479577587 11213669866361885219366381)
                    ·
                      refine ⟨4205126199885706957262393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11213669866361885219366381 4205126199885706957262393)
                      ·
                        rfl

theorem cell23_8189454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_8189454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189454 prefixEnd_8189454 := by exact prefixLift 8189454
  have htrace : WordTrace (prefixWord ++ tailWord_8189454) baseStart_8189454 baseEnd_8189454 := by
    simpa [prefixWord, tailWord_8189454, baseEnd_8189454] using wordTrace_append hprefix tailTrace_8189454
  have hstable : (prefixWord ++ tailWord_8189454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189454).length < 2 ^ (prefixWord ++ tailWord_8189454).sum := by decide
  have hdescent : baseEnd_8189454 < baseStart_8189454 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189473 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_8189473 : Nat := 118140960795 + 8189473 * 2 ^ 59
def prefixEnd_8189473 : Nat := 4983230072969 + 3 ^ 40 * 8189473 * 2
def baseEnd_8189473 : Nat := 4205135956018142382924805

theorem tailTrace_8189473 : CollatzResearch.WordTrace tailWord_8189473 prefixEnd_8189473 4205135956018142382924805 := by
  unfold tailWord_8189473
  simp only [CollatzResearch.WordTrace]
  refine ⟨298694619059945446481245073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199129746039963630987496715 298694619059945446481245073)
  ·
    refine ⟨224020964294959084860933805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298694619059945446481245073 224020964294959084860933805)
    ·
      refine ⟨84007861610609656822850177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224020964294959084860933805 84007861610609656822850177)
      ·
        refine ⟨63005896207957242617137633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84007861610609656822850177 63005896207957242617137633)
        ·
          refine ⟨47254422155967931962853225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63005896207957242617137633 47254422155967931962853225)
          ·
            refine ⟨35440816616975948972139919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47254422155967931962853225 35440816616975948972139919)
            ·
              refine ⟨53161224925463923458209879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35440816616975948972139919 53161224925463923458209879)
              ·
                refine ⟨79741837388195885187314819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53161224925463923458209879 79741837388195885187314819)
                ·
                  refine ⟨119612756082293827780972229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79741837388195885187314819 119612756082293827780972229)
                  ·
                    refine ⟨22427391765430092708932293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119612756082293827780972229 22427391765430092708932293)
                    ·
                      refine ⟨4205135956018142382924805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22427391765430092708932293 4205135956018142382924805)
                      ·
                        rfl

theorem cell23_8189473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_8189473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189473 prefixEnd_8189473 := by exact prefixLift 8189473
  have htrace : WordTrace (prefixWord ++ tailWord_8189473) baseStart_8189473 baseEnd_8189473 := by
    simpa [prefixWord, tailWord_8189473, baseEnd_8189473] using wordTrace_append hprefix tailTrace_8189473
  have hstable : (prefixWord ++ tailWord_8189473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189473).length < 2 ^ (prefixWord ++ tailWord_8189473).sum := by decide
  have hdescent : baseEnd_8189473 < baseStart_8189473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189511 : List Nat := [1, 1, 4, 1, 5, 2, 1, 2, 2, 2, 2]
def baseStart_8189511 : Nat := 118140960795 + 8189511 * 2 ^ 59
def prefixEnd_8189511 : Nat := 4983230072969 + 3 ^ 40 * 8189511 * 2
def baseEnd_8189511 : Nat := 4205155468283013234249631

theorem tailTrace_8189511 : CollatzResearch.WordTrace tailWord_8189511 prefixEnd_8189511 4205155468283013234249631 := by
  unfold tailWord_8189511
  simp only [CollatzResearch.WordTrace]
  refine ⟨298696005033807778971128387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199130670022538519314085591 298696005033807778971128387)
  ·
    refine ⟨448044007550711668456692581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298696005033807778971128387 448044007550711668456692581)
    ·
      refine ⟨84008251415758437835629859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448044007550711668456692581 84008251415758437835629859)
      ·
        refine ⟨126012377123637656753444789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84008251415758437835629859 126012377123637656753444789)
        ·
          refine ⟨11813660355341030320635449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126012377123637656753444789 11813660355341030320635449)
          ·
            refine ⟨8860245266505772740476587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11813660355341030320635449 8860245266505772740476587)
            ·
              refine ⟨13290367899758659110714881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8860245266505772740476587 13290367899758659110714881)
              ·
                refine ⟨9967775924818994333036161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13290367899758659110714881 9967775924818994333036161)
                ·
                  refine ⟨7475831943614245749777121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9967775924818994333036161 7475831943614245749777121)
                  ·
                    refine ⟨5606873957710684312332841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7475831943614245749777121 5606873957710684312332841)
                    ·
                      refine ⟨4205155468283013234249631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606873957710684312332841 4205155468283013234249631)
                      ·
                        rfl

theorem cell23_8189511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_8189511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189511 prefixEnd_8189511 := by exact prefixLift 8189511
  have htrace : WordTrace (prefixWord ++ tailWord_8189511) baseStart_8189511 baseEnd_8189511 := by
    simpa [prefixWord, tailWord_8189511, baseEnd_8189511] using wordTrace_append hprefix tailTrace_8189511
  have hstable : (prefixWord ++ tailWord_8189511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189511).length < 2 ^ (prefixWord ++ tailWord_8189511).sum := by decide
  have hdescent : baseEnd_8189511 < baseStart_8189511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189513 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 2, 5]
def baseStart_8189513 : Nat := 118140960795 + 8189513 * 2 ^ 59
def prefixEnd_8189513 : Nat := 4983230072969 + 3 ^ 40 * 8189513 * 2
def baseEnd_8189513 : Nat := 1401718831748107408808207

theorem tailTrace_8189513 : CollatzResearch.WordTrace tailWord_8189513 prefixEnd_8189513 1401718831748107408808207 := by
  unfold tailWord_8189513
  simp only [CollatzResearch.WordTrace]
  refine ⟨298696077979800533312701193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199130718653200355541800795 298696077979800533312701193)
  ·
    refine ⟨224022058484850399984525895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298696077979800533312701193 224022058484850399984525895)
    ·
      refine ⟨336033087727275599976788843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224022058484850399984525895 336033087727275599976788843)
      ·
        refine ⟨504049631590913399965183265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336033087727275599976788843 504049631590913399965183265)
        ·
          refine ⟨378037223693185049973887449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504049631590913399965183265 378037223693185049973887449)
          ·
            refine ⟨283527917769888787480415587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378037223693185049973887449 283527917769888787480415587)
            ·
              refine ⟨425291876654833181220623381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283527917769888787480415587 425291876654833181220623381)
              ·
                refine ⟨19935556718195305369716721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 425291876654833181220623381 19935556718195305369716721)
                ·
                  refine ⟨14951667538646479027287541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19935556718195305369716721 14951667538646479027287541)
                  ·
                    refine ⟨1401718831748107408808207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14951667538646479027287541 1401718831748107408808207)
                    ·
                      rfl

theorem cell23_8189513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 5].length) (baseStart_8189513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189513 prefixEnd_8189513 := by exact prefixLift 8189513
  have htrace : WordTrace (prefixWord ++ tailWord_8189513) baseStart_8189513 baseEnd_8189513 := by
    simpa [prefixWord, tailWord_8189513, baseEnd_8189513] using wordTrace_append hprefix tailTrace_8189513
  have hstable : (prefixWord ++ tailWord_8189513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189513).length < 2 ^ (prefixWord ++ tailWord_8189513).sum := by decide
  have hdescent : baseEnd_8189513 < baseStart_8189513 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189517 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 7]
def baseStart_8189517 : Nat := 118140960795 + 8189517 * 2 ^ 59
def prefixEnd_8189517 : Nat := 4983230072969 + 3 ^ 40 * 8189517 * 2
def baseEnd_8189517 : Nat := 467239838796326690086067

theorem tailTrace_8189517 : CollatzResearch.WordTrace tailWord_8189517 prefixEnd_8189517 467239838796326690086067 := by
  unfold tailWord_8189517
  simp only [CollatzResearch.WordTrace]
  refine ⟨298696223871786041995846805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199130815914524027997231203 298696223871786041995846805)
  ·
    refine ⟨14001385493989970718555319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 298696223871786041995846805 14001385493989970718555319)
    ·
      refine ⟨21002078240984956077832979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14001385493989970718555319 21002078240984956077832979)
      ·
        refine ⟨31503117361477434116749469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21002078240984956077832979 31503117361477434116749469)
        ·
          refine ⟨11813669010554037793781051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31503117361477434116749469 11813669010554037793781051)
          ·
            refine ⟨17720503515831056690671577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11813669010554037793781051 17720503515831056690671577)
            ·
              refine ⟨13290377636873292518003683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17720503515831056690671577 13290377636873292518003683)
              ·
                refine ⟨19935566455309938777005525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13290377636873292518003683 19935566455309938777005525)
                ·
                  refine ⟨467239838796326690086067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19935566455309938777005525 467239838796326690086067)
                  ·
                    rfl

theorem cell23_8189517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_8189517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189517 prefixEnd_8189517 := by exact prefixLift 8189517
  have htrace : WordTrace (prefixWord ++ tailWord_8189517) baseStart_8189517 baseEnd_8189517 := by
    simpa [prefixWord, tailWord_8189517, baseEnd_8189517] using wordTrace_append hprefix tailTrace_8189517
  have hstable : (prefixWord ++ tailWord_8189517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189517).length < 2 ^ (prefixWord ++ tailWord_8189517).sum := by decide
  have hdescent : baseEnd_8189517 < baseStart_8189517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189573 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 8]
def baseStart_8189573 : Nat := 118140960795 + 8189573 * 2 ^ 59
def prefixEnd_8189573 : Nat := 4983230072969 + 3 ^ 40 * 8189573 * 2
def baseEnd_8189573 : Nat := 467243033787065776852705

theorem tailTrace_8189573 : CollatzResearch.WordTrace tailWord_8189573 prefixEnd_8189573 467243033787065776852705 := by
  unfold tailWord_8189573
  simp only [CollatzResearch.WordTrace]
  refine ⟨298698266359583163559885373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199132177573055442373256915 298698266359583163559885373)
  ·
    refine ⟨112011849884843686334957015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298698266359583163559885373 112011849884843686334957015)
    ·
      refine ⟨168017774827265529502435523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112011849884843686334957015 168017774827265529502435523)
      ·
        refine ⟨252026662240898294253653285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168017774827265529502435523 252026662240898294253653285)
        ·
          refine ⟨47254999170168430172559991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252026662240898294253653285 47254999170168430172559991)
          ·
            refine ⟨70882498755252645258839987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47254999170168430172559991 70882498755252645258839987)
            ·
              refine ⟨106323748132878967888259981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70882498755252645258839987 106323748132878967888259981)
              ·
                refine ⟨39871405549829612958097493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106323748132878967888259981 39871405549829612958097493)
                ·
                  refine ⟨467243033787065776852705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39871405549829612958097493 467243033787065776852705)
                  ·
                    rfl

theorem cell23_8189573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_8189573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189573 prefixEnd_8189573 := by exact prefixLift 8189573
  have htrace : WordTrace (prefixWord ++ tailWord_8189573) baseStart_8189573 baseEnd_8189573 := by
    simpa [prefixWord, tailWord_8189573, baseEnd_8189573] using wordTrace_append hprefix tailTrace_8189573
  have hstable : (prefixWord ++ tailWord_8189573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189573).length < 2 ^ (prefixWord ++ tailWord_8189573).sum := by decide
  have hdescent : baseEnd_8189573 < baseStart_8189573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189577 : List Nat := [1, 2, 1, 1, 4, 1, 2, 6, 1, 4]
def baseStart_8189577 : Nat := 118140960795 + 8189577 * 2 ^ 59
def prefixEnd_8189577 : Nat := 4983230072969 + 3 ^ 40 * 8189577 * 2
def baseEnd_8189577 : Nat := 1401729786002069992008109

theorem tailTrace_8189577 : CollatzResearch.WordTrace tailWord_8189577 prefixEnd_8189577 1401729786002069992008109 := by
  unfold tailWord_8189577
  simp only [CollatzResearch.WordTrace]
  refine ⟨298698412251568672243030985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199132274834379114828687323 298698412251568672243030985)
  ·
    refine ⟨224023809188676504182273239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298698412251568672243030985 224023809188676504182273239)
    ·
      refine ⟨336035713783014756273409859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224023809188676504182273239 336035713783014756273409859)
      ·
        refine ⟨504053570674522134410114789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336035713783014756273409859 504053570674522134410114789)
        ·
          refine ⟨94510044501472900201896523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 504053570674522134410114789 94510044501472900201896523)
          ·
            refine ⟨141765066752209350302844785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94510044501472900201896523 141765066752209350302844785)
            ·
              refine ⟨106323800064157012727133589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141765066752209350302844785 106323800064157012727133589)
              ·
                refine ⟨4983928128007359971584387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106323800064157012727133589 4983928128007359971584387)
                ·
                  refine ⟨7475892192011039957376581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4983928128007359971584387 7475892192011039957376581)
                  ·
                    refine ⟨1401729786002069992008109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7475892192011039957376581 1401729786002069992008109)
                    ·
                      rfl

theorem cell23_8189577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 1, 4].length) (baseStart_8189577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189577 prefixEnd_8189577 := by exact prefixLift 8189577
  have htrace : WordTrace (prefixWord ++ tailWord_8189577) baseStart_8189577 baseEnd_8189577 := by
    simpa [prefixWord, tailWord_8189577, baseEnd_8189577] using wordTrace_append hprefix tailTrace_8189577
  have hstable : (prefixWord ++ tailWord_8189577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189577).length < 2 ^ (prefixWord ++ tailWord_8189577).sum := by decide
  have hdescent : baseEnd_8189577 < baseStart_8189577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189640 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_8189640 : Nat := 118140960795 + 8189640 * 2 ^ 59
def prefixEnd_8189640 : Nat := 4983230072969 + 3 ^ 40 * 8189640 * 2
def baseEnd_8189640 : Nat := 4205221707287443229536537

theorem tailTrace_8189640 : CollatzResearch.WordTrace tailWord_8189640 prefixEnd_8189640 4205221707287443229536537 := by
  unfold tailWord_8189640
  simp only [CollatzResearch.WordTrace]
  refine ⟨149350355025170217001287187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199133806700226956001716249 149350355025170217001287187)
  ·
    refine ⟨224025532537755325501930781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149350355025170217001287187 224025532537755325501930781)
    ·
      refine ⟨84009574701658247063224043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224025532537755325501930781 84009574701658247063224043)
      ·
        refine ⟨126014362052487370594836065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84009574701658247063224043 126014362052487370594836065)
        ·
          refine ⟨94510771539365527946127049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126014362052487370594836065 94510771539365527946127049)
          ·
            refine ⟨70883078654524145959595287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94510771539365527946127049 70883078654524145959595287)
            ·
              refine ⟨106324617981786218939392931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70883078654524145959595287 106324617981786218939392931)
              ·
                refine ⟨159486926972679328409089397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106324617981786218939392931 159486926972679328409089397)
                ·
                  refine ⟨14951899403688687038352131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159486926972679328409089397 14951899403688687038352131)
                  ·
                    refine ⟨22427849105533030557528197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14951899403688687038352131 22427849105533030557528197)
                    ·
                      refine ⟨4205221707287443229536537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22427849105533030557528197 4205221707287443229536537)
                      ·
                        rfl

theorem cell23_8189640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_8189640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189640 prefixEnd_8189640 := by exact prefixLift 8189640
  have htrace : WordTrace (prefixWord ++ tailWord_8189640) baseStart_8189640 baseEnd_8189640 := by
    simpa [prefixWord, tailWord_8189640, baseEnd_8189640] using wordTrace_append hprefix tailTrace_8189640
  have hstable : (prefixWord ++ tailWord_8189640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189640).length < 2 ^ (prefixWord ++ tailWord_8189640).sum := by decide
  have hdescent : baseEnd_8189640 < baseStart_8189640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189661 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_8189661 : Nat := 118140960795 + 8189661 * 2 ^ 59
def prefixEnd_8189661 : Nat := 4983230072969 + 3 ^ 40 * 8189661 * 2
def baseEnd_8189661 : Nat := 4205232490381187647373941

theorem tailTrace_8189661 : CollatzResearch.WordTrace tailWord_8189661 prefixEnd_8189661 4205232490381187647373941 := by
  unfold tailWord_8189661
  simp only [CollatzResearch.WordTrace]
  refine ⟨298701475983264354589088837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199134317322176236392725891 298701475983264354589088837)
  ·
    refine ⟨56006526746862066485454157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298701475983264354589088837 56006526746862066485454157)
    ·
      refine ⟨21002447530073274932045309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56006526746862066485454157 21002447530073274932045309)
      ·
        refine ⟨7875917823777478099516991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21002447530073274932045309 7875917823777478099516991)
        ·
          refine ⟨11813876735666217149275487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7875917823777478099516991 11813876735666217149275487)
          ·
            refine ⟨17720815103499325723913231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11813876735666217149275487 17720815103499325723913231)
            ·
              refine ⟨26581222655248988585869847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17720815103499325723913231 26581222655248988585869847)
              ·
                refine ⟨39871833982873482878804771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26581222655248988585869847 39871833982873482878804771)
                ·
                  refine ⟨59807750974310224318207157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39871833982873482878804771 59807750974310224318207157)
                  ·
                    refine ⟨5606976653841583529831921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59807750974310224318207157 5606976653841583529831921)
                    ·
                      refine ⟨4205232490381187647373941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5606976653841583529831921 4205232490381187647373941)
                      ·
                        rfl

theorem cell23_8189661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_8189661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189661 prefixEnd_8189661 := by exact prefixLift 8189661
  have htrace : WordTrace (prefixWord ++ tailWord_8189661) baseStart_8189661 baseEnd_8189661 := by
    simpa [prefixWord, tailWord_8189661, baseEnd_8189661] using wordTrace_append hprefix tailTrace_8189661
  have hstable : (prefixWord ++ tailWord_8189661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189661).length < 2 ^ (prefixWord ++ tailWord_8189661).sum := by decide
  have hdescent : baseEnd_8189661 < baseStart_8189661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189674 : List Nat := [3, 1, 3, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_8189674 : Nat := 118140960795 + 8189674 * 2 ^ 59
def prefixEnd_8189674 : Nat := 4983230072969 + 3 ^ 40 * 8189674 * 2
def baseEnd_8189674 : Nat := 4205239165629696096511381

theorem tailTrace_8189674 : CollatzResearch.WordTrace tailWord_8189674 prefixEnd_8189674 4205239165629696096511381 := by
  unfold tailWord_8189674
  simp only [CollatzResearch.WordTrace]
  refine ⟨74675487533054314452328019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199134633421478171872874717 74675487533054314452328019)
  ·
    refine ⟨112013231299581471678492029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74675487533054314452328019 112013231299581471678492029)
    ·
      refine ⟨42004961737343051879434511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112013231299581471678492029 42004961737343051879434511)
      ·
        refine ⟨63007442606014577819151767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42004961737343051879434511 63007442606014577819151767)
        ·
          refine ⟨94511163909021866728727651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63007442606014577819151767 94511163909021866728727651)
          ·
            refine ⟨141766745863532800093091477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94511163909021866728727651 141766745863532800093091477)
            ·
              refine ⟨6645316212353100004363663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141766745863532800093091477 6645316212353100004363663)
              ·
                refine ⟨9967974318529650006545495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645316212353100004363663 9967974318529650006545495)
                ·
                  refine ⟨14951961477794475009818243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9967974318529650006545495 14951961477794475009818243)
                  ·
                    refine ⟨22427942216691712514727365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14951961477794475009818243 22427942216691712514727365)
                    ·
                      refine ⟨4205239165629696096511381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22427942216691712514727365 4205239165629696096511381)
                      ·
                        rfl

theorem cell23_8189674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_8189674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189674 prefixEnd_8189674 := by exact prefixLift 8189674
  have htrace : WordTrace (prefixWord ++ tailWord_8189674) baseStart_8189674 baseEnd_8189674 := by
    simpa [prefixWord, tailWord_8189674, baseEnd_8189674] using wordTrace_append hprefix tailTrace_8189674
  have hstable : (prefixWord ++ tailWord_8189674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189674).length < 2 ^ (prefixWord ++ tailWord_8189674).sum := by decide
  have hdescent : baseEnd_8189674 < baseStart_8189674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189694 : List Nat := [4, 2, 2, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_8189694 : Nat := 118140960795 + 8189694 * 2 ^ 59
def prefixEnd_8189694 : Nat := 4983230072969 + 3 ^ 40 * 8189694 * 2
def baseEnd_8189694 : Nat := 4205249435242786018261289

theorem tailTrace_8189694 : CollatzResearch.WordTrace tailWord_8189694 prefixEnd_8189694 4205249435242786018261289 := by
  unfold tailWord_8189694
  simp only [CollatzResearch.WordTrace]
  refine ⟨37337834949018100153130017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199135119728096534150026757 37337834949018100153130017)
  ·
    refine ⟨28003376211763575114847513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37337834949018100153130017 28003376211763575114847513)
    ·
      refine ⟨21002532158822681336135635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28003376211763575114847513 21002532158822681336135635)
      ·
        refine ⟨31503798238234022004203453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21002532158822681336135635 31503798238234022004203453)
        ·
          refine ⟨11813924339337758251576295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31503798238234022004203453 11813924339337758251576295)
          ·
            refine ⟨17720886509006637377364443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11813924339337758251576295 17720886509006637377364443)
            ·
              refine ⟨26581329763509956066046665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17720886509006637377364443 26581329763509956066046665)
              ·
                refine ⟨19935997322632467049534999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26581329763509956066046665 19935997322632467049534999)
                ·
                  refine ⟨29903995983948700574302499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19935997322632467049534999 29903995983948700574302499)
                  ·
                    refine ⟨44855993975923050861453749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29903995983948700574302499 44855993975923050861453749)
                    ·
                      refine ⟨4205249435242786018261289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44855993975923050861453749 4205249435242786018261289)
                      ·
                        rfl

theorem cell23_8189694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_8189694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189694 prefixEnd_8189694 := by exact prefixLift 8189694
  have htrace : WordTrace (prefixWord ++ tailWord_8189694) baseStart_8189694 baseEnd_8189694 := by
    simpa [prefixWord, tailWord_8189694, baseEnd_8189694] using wordTrace_append hprefix tailTrace_8189694
  have hstable : (prefixWord ++ tailWord_8189694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189694).length < 2 ^ (prefixWord ++ tailWord_8189694).sum := by decide
  have hdescent : baseEnd_8189694 < baseStart_8189694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189707 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 3]
def baseStart_8189707 : Nat := 118140960795 + 8189707 * 2 ^ 59
def prefixEnd_8189707 : Nat := 4983230072969 + 3 ^ 40 * 8189707 * 2
def baseEnd_8189707 : Nat := 4205256110491294467398729

theorem tailTrace_8189707 : CollatzResearch.WordTrace tailWord_8189707 prefixEnd_8189707 4205256110491294467398729 := by
  unfold tailWord_8189707
  simp only [CollatzResearch.WordTrace]
  refine ⟨298703153741097704445263375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199135435827398469630175583 298703153741097704445263375)
  ·
    refine ⟨448054730611646556667895063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298703153741097704445263375 448054730611646556667895063)
    ·
      refine ⟨672082095917469835001842595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448054730611646556667895063 672082095917469835001842595)
      ·
        refine ⟨1008123143876204752502763893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672082095917469835001842595 1008123143876204752502763893)
        ·
          refine ⟨94511544738394195547134115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1008123143876204752502763893 94511544738394195547134115)
          ·
            refine ⟨141767317107591293320701173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94511544738394195547134115 141767317107591293320701173)
            ·
              refine ⟨13290685978836683748815735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141767317107591293320701173 13290685978836683748815735)
              ·
                refine ⟨19936028968255025623223603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13290685978836683748815735 19936028968255025623223603)
                ·
                  refine ⟨29904043452382538434835405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19936028968255025623223603 29904043452382538434835405)
                  ·
                    refine ⟨11214016294643451913063277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29904043452382538434835405 11214016294643451913063277)
                    ·
                      refine ⟨4205256110491294467398729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11214016294643451913063277 4205256110491294467398729)
                      ·
                        rfl

theorem cell23_8189707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 3].length) (baseStart_8189707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189707 prefixEnd_8189707 := by exact prefixLift 8189707
  have htrace : WordTrace (prefixWord ++ tailWord_8189707) baseStart_8189707 baseEnd_8189707 := by
    simpa [prefixWord, tailWord_8189707, baseEnd_8189707] using wordTrace_append hprefix tailTrace_8189707
  have hstable : (prefixWord ++ tailWord_8189707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189707).length < 2 ^ (prefixWord ++ tailWord_8189707).sum := by decide
  have hdescent : baseEnd_8189707 < baseStart_8189707 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189710 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_8189710 : Nat := 118140960795 + 8189710 * 2 ^ 59
def prefixEnd_8189710 : Nat := 4983230072969 + 3 ^ 40 * 8189710 * 2
def baseEnd_8189710 : Nat := 1401752550311085985220405

theorem tailTrace_8189710 : CollatzResearch.WordTrace tailWord_8189710 prefixEnd_8189710 1401752550311085985220405 := by
  unfold tailWord_8189710
  simp only [CollatzResearch.WordTrace]
  refine ⟨37337907895010854494702823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199135508773391223971748389 37337907895010854494702823)
  ·
    refine ⟨56006861842516281742054235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37337907895010854494702823 56006861842516281742054235)
    ·
      refine ⟨84010292763774422613081353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56006861842516281742054235 84010292763774422613081353)
      ·
        refine ⟨63007719572830816959811015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84010292763774422613081353 63007719572830816959811015)
        ·
          refine ⟨94511579359246225439716523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63007719572830816959811015 94511579359246225439716523)
          ·
            refine ⟨141767369038869338159574785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94511579359246225439716523 141767369038869338159574785)
            ·
              refine ⟨106325526779152003619681089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141767369038869338159574785 106325526779152003619681089)
              ·
                refine ⟨79744145084364002714760817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106325526779152003619681089 79744145084364002714760817)
                ·
                  refine ⟨59808108813273002036070613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79744145084364002714760817 59808108813273002036070613)
                  ·
                    refine ⟨1401752550311085985220405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59808108813273002036070613 1401752550311085985220405)
                    ·
                      rfl

theorem cell23_8189710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_8189710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189710 prefixEnd_8189710 := by exact prefixLift 8189710
  have htrace : WordTrace (prefixWord ++ tailWord_8189710) baseStart_8189710 baseEnd_8189710 := by
    simpa [prefixWord, tailWord_8189710, baseEnd_8189710] using wordTrace_append hprefix tailTrace_8189710
  have hstable : (prefixWord ++ tailWord_8189710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189710).length < 2 ^ (prefixWord ++ tailWord_8189710).sum := by decide
  have hdescent : baseEnd_8189710 < baseStart_8189710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189714 : List Nat := [3, 2, 4, 1, 1, 1, 4, 7]
def baseStart_8189714 : Nat := 118140960795 + 8189714 * 2 ^ 59
def prefixEnd_8189714 : Nat := 4983230072969 + 3 ^ 40 * 8189714 * 2
def baseEnd_8189714 : Nat := 155750359439106516296711

theorem tailTrace_8189714 : CollatzResearch.WordTrace tailWord_8189714 prefixEnd_8189714 155750359439106516296711 := by
  unfold tailWord_8189714
  simp only [CollatzResearch.WordTrace]
  refine ⟨74675852263018086160192049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199135606034714896427178797 74675852263018086160192049)
  ·
    refine ⟨56006889197263564620144037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74675852263018086160192049 56006889197263564620144037)
    ·
      refine ⟨10501291724486918366277007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56006889197263564620144037 10501291724486918366277007)
      ·
        refine ⟨15751937586730377549415511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10501291724486918366277007 15751937586730377549415511)
        ·
          refine ⟨23627906380095566324123267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15751937586730377549415511 23627906380095566324123267)
          ·
            refine ⟨35441859570143349486184901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23627906380095566324123267 35441859570143349486184901)
            ·
              refine ⟨6645348669401878028659669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35441859570143349486184901 6645348669401878028659669)
              ·
                refine ⟨155750359439106516296711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6645348669401878028659669 155750359439106516296711)
                ·
                  rfl

theorem cell23_8189714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 7].length) (baseStart_8189714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189714 prefixEnd_8189714 := by exact prefixLift 8189714
  have htrace : WordTrace (prefixWord ++ tailWord_8189714) baseStart_8189714 baseEnd_8189714 := by
    simpa [prefixWord, tailWord_8189714, baseEnd_8189714] using wordTrace_append hprefix tailTrace_8189714
  have hstable : (prefixWord ++ tailWord_8189714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189714).length < 2 ^ (prefixWord ++ tailWord_8189714).sum := by decide
  have hdescent : baseEnd_8189714 < baseStart_8189714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189720 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_8189720 : Nat := 118140960795 + 8189720 * 2 ^ 59
def prefixEnd_8189720 : Nat := 4983230072969 + 3 ^ 40 * 8189720 * 2
def baseEnd_8189720 : Nat := 4205262785739802916536169

theorem tailTrace_8189720 : CollatzResearch.WordTrace tailWord_8189720 prefixEnd_8189720 4205262785739802916536169 := by
  unfold tailWord_8189720
  simp only [CollatzResearch.WordTrace]
  refine ⟨149351813945025303832743307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199135751926700405110324409 149351813945025303832743307)
  ·
    refine ⟨224027720917537955749114961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149351813945025303832743307 224027720917537955749114961)
    ·
      refine ⟨168020790688153466811836221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224027720917537955749114961 168020790688153466811836221)
      ·
        refine ⟨63007796508057550054438583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168020790688153466811836221 63007796508057550054438583)
        ·
          refine ⟨94511694762086325081657875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63007796508057550054438583 94511694762086325081657875)
          ·
            refine ⟨141767542143129487622486813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94511694762086325081657875 141767542143129487622486813)
            ·
              refine ⟨53162828303673557858432555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141767542143129487622486813 53162828303673557858432555)
              ·
                refine ⟨79744242455510336787648833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53162828303673557858432555 79744242455510336787648833)
                ·
                  refine ⟨59808181841632752590736625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79744242455510336787648833 59808181841632752590736625)
                  ·
                    refine ⟨44856136381224564443052469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59808181841632752590736625 44856136381224564443052469)
                    ·
                      refine ⟨4205262785739802916536169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44856136381224564443052469 4205262785739802916536169)
                      ·
                        rfl

theorem cell23_8189720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_8189720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189720 prefixEnd_8189720 := by exact prefixLift 8189720
  have htrace : WordTrace (prefixWord ++ tailWord_8189720) baseStart_8189720 baseEnd_8189720 := by
    simpa [prefixWord, tailWord_8189720, baseEnd_8189720] using wordTrace_append hprefix tailTrace_8189720
  have hstable : (prefixWord ++ tailWord_8189720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189720).length < 2 ^ (prefixWord ++ tailWord_8189720).sum := by decide
  have hdescent : baseEnd_8189720 < baseStart_8189720 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189742 : List Nat := [4, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_8189742 : Nat := 118140960795 + 8189742 * 2 ^ 59
def prefixEnd_8189742 : Nat := 4983230072969 + 3 ^ 40 * 8189742 * 2
def baseEnd_8189742 : Nat := 4205274082314201830461069

theorem tailTrace_8189742 : CollatzResearch.WordTrace tailWord_8189742 prefixEnd_8189742 4205274082314201830461069 := by
  unfold tailWord_8189742
  simp only [CollatzResearch.WordTrace]
  refine ⟨37338053786996363177848435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199136286863980603615191653 37338053786996363177848435)
  ·
    refine ⟨56007080680494544766772653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37338053786996363177848435 56007080680494544766772653)
    ·
      refine ⟨21002655255185454287539745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56007080680494544766772653 21002655255185454287539745)
      ·
        refine ⟨15751991441389090715654809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21002655255185454287539745 15751991441389090715654809)
        ·
          refine ⟨11813993581041818036741107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15751991441389090715654809 11813993581041818036741107)
          ·
            refine ⟨17720990371562727055111661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11813993581041818036741107 17720990371562727055111661)
            ·
              refine ⟨6645371389336022645666873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17720990371562727055111661 6645371389336022645666873)
              ·
                refine ⟨4984028542002016984250155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6645371389336022645666873 4984028542002016984250155)
                ·
                  refine ⟨7476042813003025476375233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4984028542002016984250155 7476042813003025476375233)
                  ·
                    refine ⟨5607032109752269107281425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7476042813003025476375233 5607032109752269107281425)
                    ·
                      refine ⟨4205274082314201830461069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5607032109752269107281425 4205274082314201830461069)
                      ·
                        rfl

theorem cell23_8189742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_8189742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189742 prefixEnd_8189742 := by exact prefixLift 8189742
  have htrace : WordTrace (prefixWord ++ tailWord_8189742) baseStart_8189742 baseEnd_8189742 := by
    simpa [prefixWord, tailWord_8189742, baseEnd_8189742] using wordTrace_append hprefix tailTrace_8189742
  have hstable : (prefixWord ++ tailWord_8189742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189742).length < 2 ^ (prefixWord ++ tailWord_8189742).sum := by decide
  have hdescent : baseEnd_8189742 < baseStart_8189742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189758 : List Nat := [4, 2, 1, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_8189758 : Nat := 118140960795 + 8189758 * 2 ^ 59
def prefixEnd_8189758 : Nat := 4983230072969 + 3 ^ 40 * 8189758 * 2
def baseEnd_8189758 : Nat := 4205282298004673767860995

theorem tailTrace_8189758 : CollatzResearch.WordTrace tailWord_8189758 prefixEnd_8189758 4205282298004673767860995 := by
  unfold tailWord_8189758
  simp only [CollatzResearch.WordTrace]
  refine ⟨37338126732989117519421241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199136675909275293436913285 37338126732989117519421241)
  ·
    refine ⟨28003595049741838139565931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37338126732989117519421241 28003595049741838139565931)
    ·
      refine ⟨42005392574612757209348897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28003595049741838139565931 42005392574612757209348897)
      ·
        refine ⟨31504044430959567907011673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42005392574612757209348897 31504044430959567907011673)
        ·
          refine ⟨23628033323219675930258755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31504044430959567907011673 23628033323219675930258755)
          ·
            refine ⟨35442049984829513895388133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23628033323219675930258755 35442049984829513895388133)
            ·
              refine ⟨6645384372155533855385275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35442049984829513895388133 6645384372155533855385275)
              ·
                refine ⟨9968076558233300783077913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645384372155533855385275 9968076558233300783077913)
                ·
                  refine ⟨7476057418674975587308435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9968076558233300783077913 7476057418674975587308435)
                  ·
                    refine ⟨11214086128012463380962653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7476057418674975587308435 11214086128012463380962653)
                    ·
                      refine ⟨4205282298004673767860995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11214086128012463380962653 4205282298004673767860995)
                      ·
                        rfl

theorem cell23_8189758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_8189758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189758 prefixEnd_8189758 := by exact prefixLift 8189758
  have htrace : WordTrace (prefixWord ++ tailWord_8189758) baseStart_8189758 baseEnd_8189758 := by
    simpa [prefixWord, tailWord_8189758, baseEnd_8189758] using wordTrace_append hprefix tailTrace_8189758
  have hstable : (prefixWord ++ tailWord_8189758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189758).length < 2 ^ (prefixWord ++ tailWord_8189758).sum := by decide
  have hdescent : baseEnd_8189758 < baseStart_8189758 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189770 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 9]
def baseStart_8189770 : Nat := 118140960795 + 8189770 * 2 ^ 59
def prefixEnd_8189770 : Nat := 4983230072969 + 3 ^ 40 * 8189770 * 2
def baseEnd_8189770 : Nat := 467254273308058635656771

theorem tailTrace_8189770 : CollatzResearch.WordTrace tailWord_8189770 prefixEnd_8189770 467254273308058635656771 := by
  unfold tailWord_8189770
  simp only [CollatzResearch.WordTrace]
  refine ⟨74676362884967366551201691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199136967693246310803204509 74676362884967366551201691)
  ·
    refine ⟨112014544327451049826802537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74676362884967366551201691 112014544327451049826802537)
    ·
      refine ⟨84010908245588287370101903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112014544327451049826802537 84010908245588287370101903)
      ·
        refine ⟨126016362368382431055152855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84010908245588287370101903 126016362368382431055152855)
        ·
          refine ⟨189024543552573646582729283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126016362368382431055152855 189024543552573646582729283)
          ·
            refine ⟨283536815328860469874093925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189024543552573646582729283 283536815328860469874093925)
            ·
              refine ⟨53163152874161338101392611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283536815328860469874093925 53163152874161338101392611)
              ·
                refine ⟨79744729311242007152088917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53163152874161338101392611 79744729311242007152088917)
                ·
                  refine ⟨467254273308058635656771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79744729311242007152088917 467254273308058635656771)
                  ·
                    rfl

theorem cell23_8189770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_8189770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189770 prefixEnd_8189770 := by exact prefixLift 8189770
  have htrace : WordTrace (prefixWord ++ tailWord_8189770) baseStart_8189770 baseEnd_8189770 := by
    simpa [prefixWord, tailWord_8189770, baseEnd_8189770] using wordTrace_append hprefix tailTrace_8189770
  have hstable : (prefixWord ++ tailWord_8189770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189770).length < 2 ^ (prefixWord ++ tailWord_8189770).sum := by decide
  have hdescent : baseEnd_8189770 < baseStart_8189770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189797 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 2, 3, 3]
def baseStart_8189797 : Nat := 118140960795 + 8189797 * 2 ^ 59
def prefixEnd_8189797 : Nat := 4983230072969 + 3 ^ 40 * 8189797 * 2
def baseEnd_8189797 : Nat := 4205302323750199115273315

theorem tailTrace_8189797 : CollatzResearch.WordTrace tailWord_8189797 prefixEnd_8189797 4205302323750199115273315 := by
  unfold tailWord_8189797
  simp only [CollatzResearch.WordTrace]
  refine ⟨298706436310771649816039645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199137624207181099877359763 298706436310771649816039645)
  ·
    refine ⟨112014913616539368681014867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298706436310771649816039645 112014913616539368681014867)
    ·
      refine ⟨168022370424809053021522301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112014913616539368681014867 168022370424809053021522301)
      ·
        refine ⟨63008388909303394883070863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168022370424809053021522301 63008388909303394883070863)
        ·
          refine ⟨94512583363955092324606295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63008388909303394883070863 94512583363955092324606295)
          ·
            refine ⟨141768875045932638486909443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94512583363955092324606295 141768875045932638486909443)
            ·
              refine ⟨212653312568898957730364165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141768875045932638486909443 212653312568898957730364165)
              ·
                refine ⟨39872496106668554574443281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212653312568898957730364165 39872496106668554574443281)
                ·
                  refine ⟨29904372080001415930832461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39872496106668554574443281 29904372080001415930832461)
                  ·
                    refine ⟨11214139530000530974062173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29904372080001415930832461 11214139530000530974062173)
                    ·
                      refine ⟨4205302323750199115273315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11214139530000530974062173 4205302323750199115273315)
                      ·
                        rfl

theorem cell23_8189797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_8189797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189797 prefixEnd_8189797 := by exact prefixLift 8189797
  have htrace : WordTrace (prefixWord ++ tailWord_8189797) baseStart_8189797 baseEnd_8189797 := by
    simpa [prefixWord, tailWord_8189797, baseEnd_8189797] using wordTrace_append hprefix tailTrace_8189797
  have hstable : (prefixWord ++ tailWord_8189797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189797).length < 2 ^ (prefixWord ++ tailWord_8189797).sum := by decide
  have hdescent : baseEnd_8189797 < baseStart_8189797 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189804 : List Nat := [2, 2, 1, 1, 4, 3, 1, 4, 5]
def baseStart_8189804 : Nat := 118140960795 + 8189804 * 2 ^ 59
def prefixEnd_8189804 : Nat := 4983230072969 + 3 ^ 40 * 8189804 * 2
def baseEnd_8189804 : Nat := 467256213123864509765087

theorem tailTrace_8189804 : CollatzResearch.WordTrace tailWord_8189804 prefixEnd_8189804 467256213123864509765087 := by
  unfold tailWord_8189804
  simp only [CollatzResearch.WordTrace]
  refine ⟨149353345810873145005772233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199137794414497526674362977 149353345810873145005772233)
  ·
    refine ⟨112015009358154858754329175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149353345810873145005772233 112015009358154858754329175)
    ·
      refine ⟨168022514037232288131493763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112015009358154858754329175 168022514037232288131493763)
      ·
        refine ⟨252033771055848432197240645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168022514037232288131493763 252033771055848432197240645)
        ·
          refine ⟨47256332072971581036982621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252033771055848432197240645 47256332072971581036982621)
          ·
            refine ⟨17721124527364342888868483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47256332072971581036982621 17721124527364342888868483)
            ·
              refine ⟨26581686791046514333302725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17721124527364342888868483 26581686791046514333302725)
              ·
                refine ⟨4984066273321221437494261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26581686791046514333302725 4984066273321221437494261)
                ·
                  refine ⟨467256213123864509765087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4984066273321221437494261 467256213123864509765087)
                  ·
                    rfl

theorem cell23_8189804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 5].length) (baseStart_8189804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189804 prefixEnd_8189804 := by exact prefixLift 8189804
  have htrace : WordTrace (prefixWord ++ tailWord_8189804) baseStart_8189804 baseEnd_8189804 := by
    simpa [prefixWord, tailWord_8189804, baseEnd_8189804] using wordTrace_append hprefix tailTrace_8189804
  have hstable : (prefixWord ++ tailWord_8189804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189804).length < 2 ^ (prefixWord ++ tailWord_8189804).sum := by decide
  have hdescent : baseEnd_8189804 < baseStart_8189804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189834 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 1, 7]
def baseStart_8189834 : Nat := 118140960795 + 8189834 * 2 ^ 59
def prefixEnd_8189834 : Nat := 4983230072969 + 3 ^ 40 * 8189834 * 2
def baseEnd_8189834 : Nat := 1401773774178138490170215

theorem tailTrace_8189834 : CollatzResearch.WordTrace tailWord_8189834 prefixEnd_8189834 1401773774178138490170215 := by
  unfold tailWord_8189834
  simp only [CollatzResearch.WordTrace]
  refine ⟨74676946452909401283784139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199138523874425070090091037 74676946452909401283784139)
  ·
    refine ⟨112015419679364101925676209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74676946452909401283784139 112015419679364101925676209)
    ·
      refine ⟨84011564759523076444257157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112015419679364101925676209 84011564759523076444257157)
      ·
        refine ⟨15752168392410576833298217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84011564759523076444257157 15752168392410576833298217)
        ·
          refine ⟨11814126294307932624973663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15752168392410576833298217 11814126294307932624973663)
          ·
            refine ⟨17721189441461898937460495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11814126294307932624973663 17721189441461898937460495)
            ·
              refine ⟨26581784162192848406190743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17721189441461898937460495 26581784162192848406190743)
              ·
                refine ⟨39872676243289272609286115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26581784162192848406190743 39872676243289272609286115)
                ·
                  refine ⟨59809014364933908913929173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39872676243289272609286115 59809014364933908913929173)
                  ·
                    refine ⟨1401773774178138490170215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59809014364933908913929173 1401773774178138490170215)
                    ·
                      rfl

theorem cell23_8189834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_8189834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189834 prefixEnd_8189834 := by exact prefixLift 8189834
  have htrace : WordTrace (prefixWord ++ tailWord_8189834) baseStart_8189834 baseEnd_8189834 := by
    simpa [prefixWord, tailWord_8189834, baseEnd_8189834] using wordTrace_append hprefix tailTrace_8189834
  have hstable : (prefixWord ++ tailWord_8189834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189834).length < 2 ^ (prefixWord ++ tailWord_8189834).sum := by decide
  have hdescent : baseEnd_8189834 < baseStart_8189834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189838 : List Nat := [4, 1, 1, 5, 1, 1, 2, 3, 5]
def baseStart_8189838 : Nat := 118140960795 + 8189838 * 2 ^ 59
def prefixEnd_8189838 : Nat := 4983230072969 + 3 ^ 40 * 8189838 * 2
def baseEnd_8189838 : Nat := 467258152939670383873403

theorem tailTrace_8189838 : CollatzResearch.WordTrace tailWord_8189838 prefixEnd_8189838 467258152939670383873403 := by
  unfold tailWord_8189838
  simp only [CollatzResearch.WordTrace]
  refine ⟨37338491462952889227285271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199138621135748742545521445 37338491462952889227285271)
  ·
    refine ⟨56007737194429333840927907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37338491462952889227285271 56007737194429333840927907)
    ·
      refine ⟨84011605791644000761391861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56007737194429333840927907 84011605791644000761391861)
      ·
        refine ⟨7876088042966625071380487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84011605791644000761391861 7876088042966625071380487)
        ·
          refine ⟨11814132064449937607070731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7876088042966625071380487 11814132064449937607070731)
          ·
            refine ⟨17721198096674906410606097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11814132064449937607070731 17721198096674906410606097)
            ·
              refine ⟨13290898572506179807954573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17721198096674906410606097 13290898572506179807954573)
              ·
                refine ⟨4984086964689817427982965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13290898572506179807954573 4984086964689817427982965)
                ·
                  refine ⟨467258152939670383873403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4984086964689817427982965 467258152939670383873403)
                  ·
                    rfl

theorem cell23_8189838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_8189838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189838 prefixEnd_8189838 := by exact prefixLift 8189838
  have htrace : WordTrace (prefixWord ++ tailWord_8189838) baseStart_8189838 baseEnd_8189838 := by
    simpa [prefixWord, tailWord_8189838, baseEnd_8189838] using wordTrace_append hprefix tailTrace_8189838
  have hstable : (prefixWord ++ tailWord_8189838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189838).length < 2 ^ (prefixWord ++ tailWord_8189838).sum := by decide
  have hdescent : baseEnd_8189838 < baseStart_8189838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189887 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 3]
def baseStart_8189887 : Nat := 118140960795 + 8189887 * 2 ^ 59
def prefixEnd_8189887 : Nat := 4983230072969 + 3 ^ 40 * 8189887 * 2
def baseEnd_8189887 : Nat := 4205348537009103763147901

theorem tailTrace_8189887 : CollatzResearch.WordTrace tailWord_8189887 prefixEnd_8189887 4205348537009103763147901 := by
  unfold tailWord_8189887
  simp only [CollatzResearch.WordTrace]
  refine ⟨298709718880445595186815915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199139812586963730124543943 298709718880445595186815915)
  ·
    refine ⟨448064578320668392780223873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298709718880445595186815915 448064578320668392780223873)
    ·
      refine ⟨336048433740501294585167905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448064578320668392780223873 336048433740501294585167905)
      ·
        refine ⟨252036325305375970938875929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336048433740501294585167905 252036325305375970938875929)
        ·
          refine ⟨189027243979031978204156947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252036325305375970938875929 189027243979031978204156947)
          ·
            refine ⟨283540865968547967306235421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189027243979031978204156947 283540865968547967306235421)
            ·
              refine ⟨106327824738205487739838283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283540865968547967306235421 106327824738205487739838283)
              ·
                refine ⟨159491737107308231609757425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106327824738205487739838283 159491737107308231609757425)
                ·
                  refine ⟨119618802830481173707318069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159491737107308231609757425 119618802830481173707318069)
                  ·
                    refine ⟨11214262765357610035061069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119618802830481173707318069 11214262765357610035061069)
                    ·
                      refine ⟨4205348537009103763147901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11214262765357610035061069 4205348537009103763147901)
                      ·
                        rfl

theorem cell23_8189887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 5, 3].length) (baseStart_8189887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189887 prefixEnd_8189887 := by exact prefixLift 8189887
  have htrace : WordTrace (prefixWord ++ tailWord_8189887) baseStart_8189887 baseEnd_8189887 := by
    simpa [prefixWord, tailWord_8189887, baseEnd_8189887] using wordTrace_append hprefix tailTrace_8189887
  have hstable : (prefixWord ++ tailWord_8189887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189887).length < 2 ^ (prefixWord ++ tailWord_8189887).sum := by decide
  have hdescent : baseEnd_8189887 < baseStart_8189887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189904 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 5, 1, 3]
def baseStart_8189904 : Nat := 118140960795 + 8189904 * 2 ^ 59
def prefixEnd_8189904 : Nat := 4983230072969 + 3 ^ 40 * 8189904 * 2
def baseEnd_8189904 : Nat := 4205357266180230196635323

theorem tailTrace_8189904 : CollatzResearch.WordTrace tailWord_8189904 prefixEnd_8189904 4205357266180230196635323 := by
  unfold tailWord_8189904
  simp only [CollatzResearch.WordTrace]
  refine ⟨149355169460692003545092383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199140225947589338060123177 149355169460692003545092383)
  ·
    refine ⟨224032754191038005317638575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149355169460692003545092383 224032754191038005317638575)
    ·
      refine ⟨336049131286557007976457863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224032754191038005317638575 336049131286557007976457863)
      ·
        refine ⟨504073696929835511964686795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336049131286557007976457863 504073696929835511964686795)
        ·
          refine ⟨756110545394753267947030193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504073696929835511964686795 756110545394753267947030193)
          ·
            refine ⟨567082909046064950960272645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756110545394753267947030193 567082909046064950960272645)
            ·
              refine ⟨106328045446137178305051121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 567082909046064950960272645 106328045446137178305051121)
              ·
                refine ⟨79746034084602883728788341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106328045446137178305051121 79746034084602883728788341)
                ·
                  refine ⟨7476190695431520349573907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79746034084602883728788341 7476190695431520349573907)
                  ·
                    refine ⟨11214286043147280524360861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7476190695431520349573907 11214286043147280524360861)
                    ·
                      refine ⟨4205357266180230196635323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11214286043147280524360861 4205357266180230196635323)
                      ·
                        rfl

theorem cell23_8189904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 5, 1, 3].length) (baseStart_8189904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189904 prefixEnd_8189904 := by exact prefixLift 8189904
  have htrace : WordTrace (prefixWord ++ tailWord_8189904) baseStart_8189904 baseEnd_8189904 := by
    simpa [prefixWord, tailWord_8189904, baseEnd_8189904] using wordTrace_append hprefix tailTrace_8189904
  have hstable : (prefixWord ++ tailWord_8189904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189904).length < 2 ^ (prefixWord ++ tailWord_8189904).sum := by decide
  have hdescent : baseEnd_8189904 < baseStart_8189904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189921 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 3, 1, 3]
def baseStart_8189921 : Nat := 118140960795 + 8189921 * 2 ^ 59
def prefixEnd_8189921 : Nat := 4983230072969 + 3 ^ 40 * 8189921 * 2
def baseEnd_8189921 : Nat := 4205365995351356630122745

theorem tailTrace_8189921 : CollatzResearch.WordTrace tailWord_8189921 prefixEnd_8189921 4205365995351356630122745 := by
  unfold tailWord_8189921
  simp only [CollatzResearch.WordTrace]
  refine ⟨298710958962322418993553617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199140639308214945995702411 298710958962322418993553617)
  ·
    refine ⟨224033219221741814245165213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298710958962322418993553617 224033219221741814245165213)
    ·
      refine ⟨84012457208153180341936955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224033219221741814245165213 84012457208153180341936955)
      ·
        refine ⟨126018685812229770512905433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84012457208153180341936955 126018685812229770512905433)
        ·
          refine ⟨94514014359172327884679075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126018685812229770512905433 94514014359172327884679075)
          ·
            refine ⟨141771021538758491827018613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94514014359172327884679075 141771021538758491827018613)
            ·
              refine ⟨13291033269258608608782995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141771021538758491827018613 13291033269258608608782995)
              ·
                refine ⟨19936549903887912913174493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13291033269258608608782995 19936549903887912913174493)
                ·
                  refine ⟨7476206213957967342440435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19936549903887912913174493 7476206213957967342440435)
                  ·
                    refine ⟨11214309320936951013660653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7476206213957967342440435 11214309320936951013660653)
                    ·
                      refine ⟨4205365995351356630122745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11214309320936951013660653 4205365995351356630122745)
                      ·
                        rfl

theorem cell23_8189921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_8189921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189921 prefixEnd_8189921 := by exact prefixLift 8189921
  have htrace : WordTrace (prefixWord ++ tailWord_8189921) baseStart_8189921 baseEnd_8189921 := by
    simpa [prefixWord, tailWord_8189921, baseEnd_8189921] using wordTrace_append hprefix tailTrace_8189921
  have hstable : (prefixWord ++ tailWord_8189921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189921).length < 2 ^ (prefixWord ++ tailWord_8189921).sum := by decide
  have hdescent : baseEnd_8189921 < baseStart_8189921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189944 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 2, 6, 2]
def baseStart_8189944 : Nat := 118140960795 + 8189944 * 2 ^ 59
def prefixEnd_8189944 : Nat := 4983230072969 + 3 ^ 40 * 8189944 * 2
def baseEnd_8189944 : Nat := 4205377805406410040135139

theorem tailTrace_8189944 : CollatzResearch.WordTrace tailWord_8189944 prefixEnd_8189944 4205377805406410040135139 := by
  unfold tailWord_8189944
  simp only [CollatzResearch.WordTrace]
  refine ⟨149355898920619546960820443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199141198560826062614427257 149355898920619546960820443)
  ·
    refine ⟨224033848380929320441230665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149355898920619546960820443 224033848380929320441230665)
    ·
      refine ⟨168025386285696990330922999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224033848380929320441230665 168025386285696990330922999)
      ·
        refine ⟨252038079428545485496384499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168025386285696990330922999 252038079428545485496384499)
        ·
          refine ⟨378057119142818228244576749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252038079428545485496384499 378057119142818228244576749)
          ·
            refine ⟨141771419678556835591716281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378057119142818228244576749 141771419678556835591716281)
            ·
              refine ⟨106328564758917626693787211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141771419678556835591716281 106328564758917626693787211)
              ·
                refine ⟨159492847138376440040680817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106328564758917626693787211 159492847138376440040680817)
                ·
                  refine ⟨119619635353782330030510613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159492847138376440040680817 119619635353782330030510613)
                  ·
                    refine ⟨5607170407208546720180185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119619635353782330030510613 5607170407208546720180185)
                    ·
                      refine ⟨4205377805406410040135139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5607170407208546720180185 4205377805406410040135139)
                      ·
                        rfl

theorem cell23_8189944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 6, 2].length) (baseStart_8189944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189944 prefixEnd_8189944 := by exact prefixLift 8189944
  have htrace : WordTrace (prefixWord ++ tailWord_8189944) baseStart_8189944 baseEnd_8189944 := by
    simpa [prefixWord, tailWord_8189944, baseEnd_8189944] using wordTrace_append hprefix tailTrace_8189944
  have hstable : (prefixWord ++ tailWord_8189944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189944).length < 2 ^ (prefixWord ++ tailWord_8189944).sum := by decide
  have hdescent : baseEnd_8189944 < baseStart_8189944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189947 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 5]
def baseStart_8189947 : Nat := 118140960795 + 8189947 * 2 ^ 59
def prefixEnd_8189947 : Nat := 4983230072969 + 3 ^ 40 * 8189947 * 2
def baseEnd_8189947 : Nat := 4205379345848373528397625

theorem tailTrace_8189947 : CollatzResearch.WordTrace tailWord_8189947 prefixEnd_8189947 4205379345848373528397625 := by
  unfold tailWord_8189947
  simp only [CollatzResearch.WordTrace]
  refine ⟨298711907260228225434000095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199141271506818816956000063 298711907260228225434000095)
  ·
    refine ⟨448067860890342338151000143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298711907260228225434000095 448067860890342338151000143)
    ·
      refine ⟨672101791335513507226500215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448067860890342338151000143 672101791335513507226500215)
      ·
        refine ⟨1008152687003270260839750323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672101791335513507226500215 1008152687003270260839750323)
        ·
          refine ⟨1512229030504905391259625485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008152687003270260839750323 1512229030504905391259625485)
          ·
            refine ⟨567085886439339521722359557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1512229030504905391259625485 567085886439339521722359557)
            ·
              refine ⟨106328603707376160322942417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 567085886439339521722359557 106328603707376160322942417)
              ·
                refine ⟨79746452780532120242206813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106328603707376160322942417 79746452780532120242206813)
                ·
                  refine ⟨29904919792699545090827555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79746452780532120242206813 29904919792699545090827555)
                  ·
                    refine ⟨44857379689049317636241333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29904919792699545090827555 44857379689049317636241333)
                    ·
                      refine ⟨4205379345848373528397625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44857379689049317636241333 4205379345848373528397625)
                      ·
                        rfl

theorem cell23_8189947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 5].length) (baseStart_8189947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189947 prefixEnd_8189947 := by exact prefixLift 8189947
  have htrace : WordTrace (prefixWord ++ tailWord_8189947) baseStart_8189947 baseEnd_8189947 := by
    simpa [prefixWord, tailWord_8189947, baseEnd_8189947] using wordTrace_append hprefix tailTrace_8189947
  have hstable : (prefixWord ++ tailWord_8189947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189947).length < 2 ^ (prefixWord ++ tailWord_8189947).sum := by decide
  have hdescent : baseEnd_8189947 < baseStart_8189947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8189981 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_8189981 : Nat := 118140960795 + 8189981 * 2 ^ 59
def prefixEnd_8189981 : Nat := 4983230072969 + 3 ^ 40 * 8189981 * 2
def baseEnd_8189981 : Nat := 4205396804190626395372469

theorem tailTrace_8189981 : CollatzResearch.WordTrace tailWord_8189981 prefixEnd_8189981 4205396804190626395372469 := by
  unfold tailWord_8189981
  simp only [CollatzResearch.WordTrace]
  refine ⟨298713147342105049240737797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199142098228070032827158531 298713147342105049240737797)
  ·
    refine ⟨56008715126644696732638337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298713147342105049240737797 56008715126644696732638337)
    ·
      refine ⟨42006536344983522549478753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56008715126644696732638337 42006536344983522549478753)
      ·
        refine ⟨31504902258737641912109065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42006536344983522549478753 31504902258737641912109065)
        ·
          refine ⟨23628676694053231434081799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31504902258737641912109065 23628676694053231434081799)
          ·
            refine ⟨35443015041079847151122699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23628676694053231434081799 35443015041079847151122699)
            ·
              refine ⟨53164522561619770726684049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35443015041079847151122699 53164522561619770726684049)
              ·
                refine ⟨39873391921214828045013037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53164522561619770726684049 39873391921214828045013037)
                ·
                  refine ⟨14952521970455560516879889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39873391921214828045013037 14952521970455560516879889)
                  ·
                    refine ⟨11214391477841670387659917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14952521970455560516879889 11214391477841670387659917)
                    ·
                      refine ⟨4205396804190626395372469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11214391477841670387659917 4205396804190626395372469)
                      ·
                        rfl

theorem cell23_8189981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_8189981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8189981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8189981 prefixEnd_8189981 := by exact prefixLift 8189981
  have htrace : WordTrace (prefixWord ++ tailWord_8189981) baseStart_8189981 baseEnd_8189981 := by
    simpa [prefixWord, tailWord_8189981, baseEnd_8189981] using wordTrace_append hprefix tailTrace_8189981
  have hstable : (prefixWord ++ tailWord_8189981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8189981).length < 2 ^ (prefixWord ++ tailWord_8189981).sum := by decide
  have hdescent : baseEnd_8189981 < baseStart_8189981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8189981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190027 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 3, 8]
def baseStart_8190027 : Nat := 118140960795 + 8190027 * 2 ^ 59
def prefixEnd_8190027 : Nat := 4983230072969 + 3 ^ 40 * 8190027 * 2
def baseEnd_8190027 : Nat := 1401806808100244405132419

theorem tailTrace_8190027 : CollatzResearch.WordTrace tailWord_8190027 prefixEnd_8190027 1401806808100244405132419 := by
  unfold tailWord_8190027
  simp only [CollatzResearch.WordTrace]
  refine ⟨298714825099938399096912335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199143216733292266064608223 298714825099938399096912335)
  ·
    refine ⟨448072237649907598645368503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298714825099938399096912335 448072237649907598645368503)
    ·
      refine ⟨672108356474861397968052755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448072237649907598645368503 672108356474861397968052755)
      ·
        refine ⟨1008162534712292096952079133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672108356474861397968052755 1008162534712292096952079133)
        ·
          refine ⟨378060950517109536357029675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1008162534712292096952079133 378060950517109536357029675)
          ·
            refine ⟨567091425775664304535544513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378060950517109536357029675 567091425775664304535544513)
            ·
              refine ⟨425318569331748228401658385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567091425775664304535544513 425318569331748228401658385)
              ·
                refine ⟨318988926998811171301243789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425318569331748228401658385 318988926998811171301243789)
                ·
                  refine ⟨119620847624554189237966421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318988926998811171301243789 119620847624554189237966421)
                  ·
                    refine ⟨1401806808100244405132419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119620847624554189237966421 1401806808100244405132419)
                    ·
                      rfl

theorem cell23_8190027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 8].length) (baseStart_8190027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190027 prefixEnd_8190027 := by exact prefixLift 8190027
  have htrace : WordTrace (prefixWord ++ tailWord_8190027) baseStart_8190027 baseEnd_8190027 := by
    simpa [prefixWord, tailWord_8190027, baseEnd_8190027] using wordTrace_append hprefix tailTrace_8190027
  have hstable : (prefixWord ++ tailWord_8190027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190027).length < 2 ^ (prefixWord ++ tailWord_8190027).sum := by decide
  have hdescent : baseEnd_8190027 < baseStart_8190027 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190028 : List Nat := [2, 2, 1, 3, 1, 1, 5, 2, 2, 1, 3]
def baseStart_8190028 : Nat := 118140960795 + 8190028 * 2 ^ 59
def prefixEnd_8190028 : Nat := 4983230072969 + 3 ^ 40 * 8190028 * 2
def baseEnd_8190028 : Nat := 4205420937781387711484753

theorem tailTrace_8190028 : CollatzResearch.WordTrace tailWord_8190028 prefixEnd_8190028 4205420937781387711484753 := by
  unfold tailWord_8190028
  simp only [CollatzResearch.WordTrace]
  refine ⟨149357430786467388133849369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199143241048623184178465825 149357430786467388133849369)
  ·
    refine ⟨112018073089850541100387027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149357430786467388133849369 112018073089850541100387027)
    ·
      refine ⟨168027109634775811650580541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112018073089850541100387027 168027109634775811650580541)
      ·
        refine ⟨63010166113040929368967703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168027109634775811650580541 63010166113040929368967703)
        ·
          refine ⟨94515249169561394053451555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63010166113040929368967703 94515249169561394053451555)
          ·
            refine ⟨141772873754342091080177333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94515249169561394053451555 141772873754342091080177333)
            ·
              refine ⟨13291206914469571038766625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141772873754342091080177333 13291206914469571038766625)
              ·
                refine ⟨9968405185852178279074969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13291206914469571038766625 9968405185852178279074969)
                ·
                  refine ⟨7476303889389133709306227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9968405185852178279074969 7476303889389133709306227)
                  ·
                    refine ⟨11214455834083700563959341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7476303889389133709306227 11214455834083700563959341)
                    ·
                      refine ⟨4205420937781387711484753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11214455834083700563959341 4205420937781387711484753)
                      ·
                        rfl

theorem cell23_8190028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_8190028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190028 prefixEnd_8190028 := by exact prefixLift 8190028
  have htrace : WordTrace (prefixWord ++ tailWord_8190028) baseStart_8190028 baseEnd_8190028 := by
    simpa [prefixWord, tailWord_8190028, baseEnd_8190028] using wordTrace_append hprefix tailTrace_8190028
  have hstable : (prefixWord ++ tailWord_8190028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190028).length < 2 ^ (prefixWord ++ tailWord_8190028).sum := by decide
  have hdescent : baseEnd_8190028 < baseStart_8190028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190045 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_8190045 : Nat := 118140960795 + 8190045 * 2 ^ 59
def prefixEnd_8190045 : Nat := 4983230072969 + 3 ^ 40 * 8190045 * 2
def baseEnd_8190045 : Nat := 4205429666952514144972175

theorem tailTrace_8190045 : CollatzResearch.WordTrace tailWord_8190045 prefixEnd_8190045 4205429666952514144972175 := by
  unfold tailWord_8190045
  simp only [CollatzResearch.WordTrace]
  refine ⟨298715481613873188171067589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199143654409248792114045059 298715481613873188171067589)
  ·
    refine ⟨56009152802601222782075173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 298715481613873188171067589 56009152802601222782075173)
    ·
      refine ⟨10501716150487729271639095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56009152802601222782075173 10501716150487729271639095)
      ·
        refine ⟨15752574225731593907458643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10501716150487729271639095 15752574225731593907458643)
        ·
          refine ⟨23628861338597390861187965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15752574225731593907458643 23628861338597390861187965)
          ·
            refine ⟨8860823001974021572945487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23628861338597390861187965 8860823001974021572945487)
            ·
              refine ⟨13291234502961032359418231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8860823001974021572945487 13291234502961032359418231)
              ·
                refine ⟨19936851754441548539127347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13291234502961032359418231 19936851754441548539127347)
                ·
                  refine ⟨29905277631662322808691021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19936851754441548539127347 29905277631662322808691021)
                  ·
                    refine ⟨11214479111873371053259133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29905277631662322808691021 11214479111873371053259133)
                    ·
                      refine ⟨4205429666952514144972175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11214479111873371053259133 4205429666952514144972175)
                      ·
                        rfl

theorem cell23_8190045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_8190045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190045 prefixEnd_8190045 := by exact prefixLift 8190045
  have htrace : WordTrace (prefixWord ++ tailWord_8190045) baseStart_8190045 baseEnd_8190045 := by
    simpa [prefixWord, tailWord_8190045, baseEnd_8190045] using wordTrace_append hprefix tailTrace_8190045
  have hstable : (prefixWord ++ tailWord_8190045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190045).length < 2 ^ (prefixWord ++ tailWord_8190045).sum := by decide
  have hdescent : baseEnd_8190045 < baseStart_8190045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190084 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_8190084 : Nat := 118140960795 + 8190084 * 2 ^ 59
def prefixEnd_8190084 : Nat := 4983230072969 + 3 ^ 40 * 8190084 * 2
def baseEnd_8190084 : Nat := 4205449692698039492384495

theorem tailTrace_8190084 : CollatzResearch.WordTrace tailWord_8190084 prefixEnd_8190084 4205449692698039492384495 := by
  unfold tailWord_8190084
  simp only [CollatzResearch.WordTrace]
  refine ⟨149358452030365948915868653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199144602707154598554491537 149358452030365948915868653)
  ·
    refine ⟨56009419511387230843450745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149358452030365948915868653 56009419511387230843450745)
    ·
      refine ⟨42007064633540423132588059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56009419511387230843450745 42007064633540423132588059)
      ·
        refine ⟨63010596950310634698882089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42007064633540423132588059 63010596950310634698882089)
        ·
          refine ⟨47257947712732976024161567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63010596950310634698882089 47257947712732976024161567)
          ·
            refine ⟨70886921569099464036242351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47257947712732976024161567 70886921569099464036242351)
            ·
              refine ⟨106330382353649196054363527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70886921569099464036242351 106330382353649196054363527)
              ·
                refine ⟨159495573530473794081545291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106330382353649196054363527 159495573530473794081545291)
                ·
                  refine ⟨239243360295710691122317937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159495573530473794081545291 239243360295710691122317937)
                  ·
                    refine ⟨179432520221783018341738453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 239243360295710691122317937 179432520221783018341738453)
                    ·
                      refine ⟨4205449692698039492384495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179432520221783018341738453 4205449692698039492384495)
                      ·
                        rfl

theorem cell23_8190084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_8190084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190084 prefixEnd_8190084 := by exact prefixLift 8190084
  have htrace : WordTrace (prefixWord ++ tailWord_8190084) baseStart_8190084 baseEnd_8190084 := by
    simpa [prefixWord, tailWord_8190084, baseEnd_8190084] using wordTrace_append hprefix tailTrace_8190084
  have hstable : (prefixWord ++ tailWord_8190084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190084).length < 2 ^ (prefixWord ++ tailWord_8190084).sum := by decide
  have hdescent : baseEnd_8190084 < baseStart_8190084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190124 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_8190124 : Nat := 118140960795 + 8190124 * 2 ^ 59
def prefixEnd_8190124 : Nat := 4983230072969 + 3 ^ 40 * 8190124 * 2
def baseEnd_8190124 : Nat := 4205470231924219335884311

theorem tailTrace_8190124 : CollatzResearch.WordTrace tailWord_8190124 prefixEnd_8190124 4205470231924219335884311 := by
  unfold tailWord_8190124
  simp only [CollatzResearch.WordTrace]
  refine ⟨149359181490293492331596713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199145575320391323108795617 149359181490293492331596713)
  ·
    refine ⟨112019386117720119248697535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149359181490293492331596713 112019386117720119248697535)
    ·
      refine ⟨168029079176580178873046303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112019386117720119248697535 168029079176580178873046303)
      ·
        refine ⟨252043618764870268309569455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168029079176580178873046303 252043618764870268309569455)
        ·
          refine ⟨378065428147305402464354183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252043618764870268309569455 378065428147305402464354183)
          ·
            refine ⟨567098142220958103696531275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378065428147305402464354183 567098142220958103696531275)
            ·
              refine ⟨850647213331437155544796913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567098142220958103696531275 850647213331437155544796913)
              ·
                refine ⟨637985409998577866658597685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850647213331437155544796913 637985409998577866658597685)
                ·
                  refine ⟨59811132187366674999243533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 637985409998577866658597685 59811132187366674999243533)
                  ·
                    refine ⟨22429174570262503124716325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59811132187366674999243533 22429174570262503124716325)
                    ·
                      refine ⟨4205470231924219335884311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22429174570262503124716325 4205470231924219335884311)
                      ·
                        rfl

theorem cell23_8190124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_8190124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190124 prefixEnd_8190124 := by exact prefixLift 8190124
  have htrace : WordTrace (prefixWord ++ tailWord_8190124) baseStart_8190124 baseEnd_8190124 := by
    simpa [prefixWord, tailWord_8190124, baseEnd_8190124] using wordTrace_append hprefix tailTrace_8190124
  have hstable : (prefixWord ++ tailWord_8190124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190124).length < 2 ^ (prefixWord ++ tailWord_8190124).sum := by decide
  have hdescent : baseEnd_8190124 < baseStart_8190124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190142 : List Nat := [4, 2, 1, 1, 4, 2, 2, 2, 5]
def baseStart_8190142 : Nat := 118140960795 + 8190142 * 2 ^ 59
def prefixEnd_8190142 : Nat := 4983230072969 + 3 ^ 40 * 8190142 * 2
def baseEnd_8190142 : Nat := 467275497175111140606581

theorem tailTrace_8190142 : CollatzResearch.WordTrace tailWord_8190142 prefixEnd_8190142 467275497175111140606581 := by
  unfold tailWord_8190142
  simp only [CollatzResearch.WordTrace]
  refine ⟨37339877436815221717168585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199146012996347849158232453 37339877436815221717168585)
  ·
    refine ⟨28004908077611416287876439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37339877436815221717168585 28004908077611416287876439)
    ·
      refine ⟨42007362116417124431814659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28004908077611416287876439 42007362116417124431814659)
      ·
        refine ⟨63011043174625686647721989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42007362116417124431814659 63011043174625686647721989)
        ·
          refine ⟨11814570595242316246447873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63011043174625686647721989 11814570595242316246447873)
          ·
            refine ⟨8860927946431737184835905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11814570595242316246447873 8860927946431737184835905)
            ·
              refine ⟨6645695959823802888626929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8860927946431737184835905 6645695959823802888626929)
              ·
                refine ⟨4984271969867852166470197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6645695959823802888626929 4984271969867852166470197)
                ·
                  refine ⟨467275497175111140606581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4984271969867852166470197 467275497175111140606581)
                  ·
                    rfl

theorem cell23_8190142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_8190142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190142 prefixEnd_8190142 := by exact prefixLift 8190142
  have htrace : WordTrace (prefixWord ++ tailWord_8190142) baseStart_8190142 baseEnd_8190142 := by
    simpa [prefixWord, tailWord_8190142, baseEnd_8190142] using wordTrace_append hprefix tailTrace_8190142
  have hstable : (prefixWord ++ tailWord_8190142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190142).length < 2 ^ (prefixWord ++ tailWord_8190142).sum := by decide
  have hdescent : baseEnd_8190142 < baseStart_8190142 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190158 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2]
def baseStart_8190158 : Nat := 118140960795 + 8190158 * 2 ^ 59
def prefixEnd_8190158 : Nat := 4983230072969 + 3 ^ 40 * 8190158 * 2
def baseEnd_8190158 : Nat := 4205487690266472202859155

theorem tailTrace_8190158 : CollatzResearch.WordTrace tailWord_8190158 prefixEnd_8190158 4205487690266472202859155 := by
  unfold tailWord_8190158
  simp only [CollatzResearch.WordTrace]
  refine ⟨37339950382807976058741391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199146402041642538979954085 37339950382807976058741391)
  ·
    refine ⟨56009925574211964088112087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37339950382807976058741391 56009925574211964088112087)
    ·
      refine ⟨84014888361317946132168131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56009925574211964088112087 84014888361317946132168131)
      ·
        refine ⟨126022332541976919198252197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84014888361317946132168131 126022332541976919198252197)
        ·
          refine ⟨23629187351620672349672287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126022332541976919198252197 23629187351620672349672287)
          ·
            refine ⟨35443781027431008524508431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23629187351620672349672287 35443781027431008524508431)
            ·
              refine ⟨53165671541146512786762647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35443781027431008524508431 53165671541146512786762647)
              ·
                refine ⟨79748507311719769180143971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53165671541146512786762647 79748507311719769180143971)
                ·
                  refine ⟨119622760967579653770215957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79748507311719769180143971 119622760967579653770215957)
                  ·
                    refine ⟨5607316920355296270478873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119622760967579653770215957 5607316920355296270478873)
                    ·
                      refine ⟨4205487690266472202859155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5607316920355296270478873 4205487690266472202859155)
                      ·
                        rfl

theorem cell23_8190158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_8190158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190158 prefixEnd_8190158 := by exact prefixLift 8190158
  have htrace : WordTrace (prefixWord ++ tailWord_8190158) baseStart_8190158 baseEnd_8190158 := by
    simpa [prefixWord, tailWord_8190158, baseEnd_8190158] using wordTrace_append hprefix tailTrace_8190158
  have hstable : (prefixWord ++ tailWord_8190158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190158).length < 2 ^ (prefixWord ++ tailWord_8190158).sum := by decide
  have hdescent : baseEnd_8190158 < baseStart_8190158 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190161 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 4, 2, 3]
def baseStart_8190161 : Nat := 118140960795 + 8190161 * 2 ^ 59
def prefixEnd_8190161 : Nat := 4983230072969 + 3 ^ 40 * 8190161 * 2
def baseEnd_8190161 : Nat := 4205489230708435691121641

theorem tailTrace_8190161 : CollatzResearch.WordTrace tailWord_8190161 prefixEnd_8190161 4205489230708435691121641 := by
  unfold tailWord_8190161
  simp only [CollatzResearch.WordTrace]
  refine ⟨298719712481452939982290337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199146474987635293321526891 298719712481452939982290337)
  ·
    refine ⟨224039784361089704986717753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298719712481452939982290337 224039784361089704986717753)
    ·
      refine ⟨168029838270817278740038315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224039784361089704986717753 168029838270817278740038315)
      ·
        refine ⟨252044757406225918110057473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168029838270817278740038315 252044757406225918110057473)
        ·
          refine ⟨189033568054669438582543105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252044757406225918110057473 189033568054669438582543105)
          ·
            refine ⟨141775176041002078936907329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189033568054669438582543105 141775176041002078936907329)
            ·
              refine ⟨106331382030751559202680497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141775176041002078936907329 106331382030751559202680497)
              ·
                refine ⟨79748536523063669402010373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106331382030751559202680497 79748536523063669402010373)
                ·
                  refine ⟨14952850598074438012876945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79748536523063669402010373 14952850598074438012876945)
                  ·
                    refine ⟨11214637948555828509657709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14952850598074438012876945 11214637948555828509657709)
                    ·
                      refine ⟨4205489230708435691121641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11214637948555828509657709 4205489230708435691121641)
                      ·
                        rfl

theorem cell23_8190161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_8190161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190161 prefixEnd_8190161 := by exact prefixLift 8190161
  have htrace : WordTrace (prefixWord ++ tailWord_8190161) baseStart_8190161 baseEnd_8190161 := by
    simpa [prefixWord, tailWord_8190161, baseEnd_8190161] using wordTrace_append hprefix tailTrace_8190161
  have hstable : (prefixWord ++ tailWord_8190161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190161).length < 2 ^ (prefixWord ++ tailWord_8190161).sum := by decide
  have hdescent : baseEnd_8190161 < baseStart_8190161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190168 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 3, 4]
def baseStart_8190168 : Nat := 118140960795 + 8190168 * 2 ^ 59
def prefixEnd_8190168 : Nat := 4983230072969 + 3 ^ 40 * 8190168 * 2
def baseEnd_8190168 : Nat := 1401830941691005721244703

theorem tailTrace_8190168 : CollatzResearch.WordTrace tailWord_8190168 prefixEnd_8190168 1401830941691005721244703 := by
  unfold tailWord_8190168
  simp only [CollatzResearch.WordTrace]
  refine ⟨149359983896213790088897579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199146645194951720118530105 149359983896213790088897579)
  ·
    refine ⟨224039975844320685133346369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149359983896213790088897579 224039975844320685133346369)
    ·
      refine ⟨168029981883240513850009777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224039975844320685133346369 168029981883240513850009777)
      ·
        refine ⟨126022486412430385387507333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168029981883240513850009777 126022486412430385387507333)
        ·
          refine ⟨23629216202330697260157625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126022486412430385387507333 23629216202330697260157625)
          ·
            refine ⟨17721912151748022945118219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23629216202330697260157625 17721912151748022945118219)
            ·
              refine ⟨26582868227622034417677329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17721912151748022945118219 26582868227622034417677329)
              ·
                refine ⟨19937151170716525813257997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26582868227622034417677329 19937151170716525813257997)
                ·
                  refine ⟨7476431689018697179971749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19937151170716525813257997 7476431689018697179971749)
                  ·
                    refine ⟨1401830941691005721244703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7476431689018697179971749 1401830941691005721244703)
                    ·
                      rfl

theorem cell23_8190168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_8190168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190168 prefixEnd_8190168 := by exact prefixLift 8190168
  have htrace : WordTrace (prefixWord ++ tailWord_8190168) baseStart_8190168 baseEnd_8190168 := by
    simpa [prefixWord, tailWord_8190168, baseEnd_8190168] using wordTrace_append hprefix tailTrace_8190168
  have hstable : (prefixWord ++ tailWord_8190168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190168).length < 2 ^ (prefixWord ++ tailWord_8190168).sum := by decide
  have hdescent : baseEnd_8190168 < baseStart_8190168 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190172 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 2, 5]
def baseStart_8190172 : Nat := 118140960795 + 8190172 * 2 ^ 59
def prefixEnd_8190172 : Nat := 4983230072969 + 3 ^ 40 * 8190172 * 2
def baseEnd_8190172 : Nat := 1401831626331878382694697

theorem tailTrace_8190172 : CollatzResearch.WordTrace tailWord_8190172 prefixEnd_8190172 1401831626331878382694697 := by
  unfold tailWord_8190172
  simp only [CollatzResearch.WordTrace]
  refine ⟨149360056842206544430470385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199146742456275392573960513 149360056842206544430470385)
  ·
    refine ⟨112020042631654908322852789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149360056842206544430470385 112020042631654908322852789)
    ·
      refine ⟨10501878996717647655267449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112020042631654908322852789 10501878996717647655267449)
      ·
        refine ⟨7876409247538235741450587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10501878996717647655267449 7876409247538235741450587)
        ·
          refine ⟨11814613871307353612175881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7876409247538235741450587 11814613871307353612175881)
          ·
            refine ⟨8860960403480515209131911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11814613871307353612175881 8860960403480515209131911)
            ·
              refine ⟨13291440605220772813697867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8860960403480515209131911 13291440605220772813697867)
              ·
                refine ⟨19937160907831159220546801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13291440605220772813697867 19937160907831159220546801)
                ·
                  refine ⟨14952870680873369415410101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19937160907831159220546801 14952870680873369415410101)
                  ·
                    refine ⟨1401831626331878382694697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14952870680873369415410101 1401831626331878382694697)
                    ·
                      rfl

theorem cell23_8190172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_8190172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190172 prefixEnd_8190172 := by exact prefixLift 8190172
  have htrace : WordTrace (prefixWord ++ tailWord_8190172) baseStart_8190172 baseEnd_8190172 := by
    simpa [prefixWord, tailWord_8190172, baseEnd_8190172] using wordTrace_append hprefix tailTrace_8190172
  have hstable : (prefixWord ++ tailWord_8190172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190172).length < 2 ^ (prefixWord ++ tailWord_8190172).sum := by decide
  have hdescent : baseEnd_8190172 < baseStart_8190172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190198 : List Nat := [5, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_8190198 : Nat := 118140960795 + 8190198 * 2 ^ 59
def prefixEnd_8190198 : Nat := 4983230072969 + 3 ^ 40 * 8190198 * 2
def baseEnd_8190198 : Nat := 467278692165850227373219

theorem tailTrace_8190198 : CollatzResearch.WordTrace tailWord_8190198 prefixEnd_8190198 467278692165850227373219 := by
  unfold tailWord_8190198
  simp only [CollatzResearch.WordTrace]
  refine ⟨18670066373894930956336703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199147374654879263534258165 18670066373894930956336703)
  ·
    refine ⟨28005099560842396434505055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18670066373894930956336703 28005099560842396434505055)
    ·
      refine ⟨42007649341263594651757583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28005099560842396434505055 42007649341263594651757583)
      ·
        refine ⟨63011474011895391977636375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42007649341263594651757583 63011474011895391977636375)
        ·
          refine ⟨94517211017843087966454563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63011474011895391977636375 94517211017843087966454563)
          ·
            refine ⟨141775816526764631949681845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94517211017843087966454563 141775816526764631949681845)
            ·
              refine ⟨13291482799384184245282673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141775816526764631949681845 13291482799384184245282673)
              ·
                refine ⟨9968612099538138183962005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13291482799384184245282673 9968612099538138183962005)
                ·
                  refine ⟨467278692165850227373219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9968612099538138183962005 467278692165850227373219)
                  ·
                    rfl

theorem cell23_8190198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_8190198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190198 prefixEnd_8190198 := by exact prefixLift 8190198
  have htrace : WordTrace (prefixWord ++ tailWord_8190198) baseStart_8190198 baseEnd_8190198 := by
    simpa [prefixWord, tailWord_8190198, baseEnd_8190198] using wordTrace_append hprefix tailTrace_8190198
  have hstable : (prefixWord ++ tailWord_8190198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190198).length < 2 ^ (prefixWord ++ tailWord_8190198).sum := by decide
  have hdescent : baseEnd_8190198 < baseStart_8190198 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190208 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 3, 1, 3]
def baseStart_8190208 : Nat := 118140960795 + 8190208 * 2 ^ 59
def prefixEnd_8190208 : Nat := 4983230072969 + 3 ^ 40 * 8190208 * 2
def baseEnd_8190208 : Nat := 4205513364299197007233925

theorem tailTrace_8190208 : CollatzResearch.WordTrace tailWord_8190208 prefixEnd_8190208 4205513364299197007233925 := by
  unfold tailWord_8190208
  simp only [CollatzResearch.WordTrace]
  refine ⟨149360713356141333504625639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199147617808188444672834185 149360713356141333504625639)
  ·
    refine ⟨224041070034212000256938459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149360713356141333504625639 224041070034212000256938459)
    ·
      refine ⟨336061605051318000385407689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224041070034212000256938459 336061605051318000385407689)
      ·
        refine ⟨252046203788488500289055767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336061605051318000385407689 252046203788488500289055767)
        ·
          refine ⟨378069305682732750433583651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252046203788488500289055767 378069305682732750433583651)
          ·
            refine ⟨567103958524099125650375477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378069305682732750433583651 567103958524099125650375477)
            ·
              refine ⟨53165996111634293029722701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 567103958524099125650375477 53165996111634293029722701)
              ·
                refine ⟨19937248541862859886146013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53165996111634293029722701 19937248541862859886146013)
                ·
                  refine ⟨7476468203198572457304755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19937248541862859886146013 7476468203198572457304755)
                  ·
                    refine ⟨11214702304797858685957133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7476468203198572457304755 11214702304797858685957133)
                    ·
                      refine ⟨4205513364299197007233925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11214702304797858685957133 4205513364299197007233925)
                      ·
                        rfl

theorem cell23_8190208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_8190208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190208 prefixEnd_8190208 := by exact prefixLift 8190208
  have htrace : WordTrace (prefixWord ++ tailWord_8190208) baseStart_8190208 baseEnd_8190208 := by
    simpa [prefixWord, tailWord_8190208, baseEnd_8190208] using wordTrace_append hprefix tailTrace_8190208
  have hstable : (prefixWord ++ tailWord_8190208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190208).length < 2 ^ (prefixWord ++ tailWord_8190208).sum := by decide
  have hdescent : baseEnd_8190208 < baseStart_8190208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190218 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2]
def baseStart_8190218 : Nat := 118140960795 + 8190218 * 2 ^ 59
def prefixEnd_8190218 : Nat := 4983230072969 + 3 ^ 40 * 8190218 * 2
def baseEnd_8190218 : Nat := 4205518499105741968108879

theorem tailTrace_8190218 : CollatzResearch.WordTrace tailWord_8190218 prefixEnd_8190218 4205518499105741968108879 := by
  unfold tailWord_8190218
  simp only [CollatzResearch.WordTrace]
  refine ⟨74680447860561609679278827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199147860961497625811410205 74680447860561609679278827)
  ·
    refine ⟨112020671790842414518918241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74680447860561609679278827 112020671790842414518918241)
    ·
      refine ⟨84015503843131810889188681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112020671790842414518918241 84015503843131810889188681)
      ·
        refine ⟨63011627882348858166891511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84015503843131810889188681 63011627882348858166891511)
        ·
          refine ⟨94517441823523287250337267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63011627882348858166891511 94517441823523287250337267)
          ·
            refine ⟨141776162735284930875505901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94517441823523287250337267 141776162735284930875505901)
            ·
              refine ⟨53166061025731849078314713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141776162735284930875505901 53166061025731849078314713)
              ·
                refine ⟨39874545769298886808736035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53166061025731849078314713 39874545769298886808736035)
                ·
                  refine ⟨59811818653948330213104053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39874545769298886808736035 59811818653948330213104053)
                  ·
                    refine ⟨5607357998807655957478505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59811818653948330213104053 5607357998807655957478505)
                    ·
                      refine ⟨4205518499105741968108879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5607357998807655957478505 4205518499105741968108879)
                      ·
                        rfl

theorem cell23_8190218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_8190218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190218 prefixEnd_8190218 := by exact prefixLift 8190218
  have htrace : WordTrace (prefixWord ++ tailWord_8190218) baseStart_8190218 baseEnd_8190218 := by
    simpa [prefixWord, tailWord_8190218, baseEnd_8190218] using wordTrace_append hprefix tailTrace_8190218
  have hstable : (prefixWord ++ tailWord_8190218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190218).length < 2 ^ (prefixWord ++ tailWord_8190218).sum := by decide
  have hdescent : baseEnd_8190218 < baseStart_8190218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190241 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 1, 6]
def baseStart_8190241 : Nat := 118140960795 + 8190241 * 2 ^ 59
def prefixEnd_8190241 : Nat := 4983230072969 + 3 ^ 40 * 8190241 * 2
def baseEnd_8190241 : Nat := 1401843436386931792707091

theorem tailTrace_8190241 : CollatzResearch.WordTrace tailWord_8190241 prefixEnd_8190241 1401843436386931792707091 := by
  unfold tailWord_8190241
  simp only [CollatzResearch.WordTrace]
  refine ⟨298722630321163113645202577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199148420214108742430135051 298722630321163113645202577)
  ·
    refine ⟨224041972740872335233901933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298722630321163113645202577 224041972740872335233901933)
    ·
      refine ⟨84015739777827125712713225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224041972740872335233901933 84015739777827125712713225)
      ·
        refine ⟨63011804833370344284534919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84015739777827125712713225 63011804833370344284534919)
        ·
          refine ⟨94517707250055516426802379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63011804833370344284534919 94517707250055516426802379)
          ·
            refine ⟨141776560875083274640203569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94517707250055516426802379 141776560875083274640203569)
            ·
              refine ⟨106332420656312455980152677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141776560875083274640203569 106332420656312455980152677)
              ·
                refine ⟨19937328873058585496278627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106332420656312455980152677 19937328873058585496278627)
                ·
                  refine ⟨29905993309587878244417941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19937328873058585496278627 29905993309587878244417941)
                  ·
                    refine ⟨1401843436386931792707091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29905993309587878244417941 1401843436386931792707091)
                    ·
                      rfl

theorem cell23_8190241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_8190241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190241 prefixEnd_8190241 := by exact prefixLift 8190241
  have htrace : WordTrace (prefixWord ++ tailWord_8190241) baseStart_8190241 baseEnd_8190241 := by
    simpa [prefixWord, tailWord_8190241, baseEnd_8190241] using wordTrace_append hprefix tailTrace_8190241
  have hstable : (prefixWord ++ tailWord_8190241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190241).length < 2 ^ (prefixWord ++ tailWord_8190241).sum := by decide
  have hdescent : baseEnd_8190241 < baseStart_8190241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190261 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_8190261 : Nat := 118140960795 + 8190261 * 2 ^ 59
def prefixEnd_8190261 : Nat := 4983230072969 + 3 ^ 40 * 8190261 * 2
def baseEnd_8190261 : Nat := 4205540578773885299871181

theorem tailTrace_8190261 : CollatzResearch.WordTrace tailWord_8190261 prefixEnd_8190261 4205540578773885299871181 := by
  unfold tailWord_8190261
  simp only [CollatzResearch.WordTrace]
  refine ⟨298723359781090657060930637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199148906520727104707287091 298723359781090657060930637)
  ·
    refine ⟨112021259917908996397848989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298723359781090657060930637 112021259917908996397848989)
    ·
      refine ⟨42007972469215873649193371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112021259917908996397848989 42007972469215873649193371)
      ·
        refine ⟨63011958703823810473790057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42007972469215873649193371 63011958703823810473790057)
        ·
          refine ⟨47258969027867857855342543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63011958703823810473790057 47258969027867857855342543)
          ·
            refine ⟨70888453541801786783013815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47258969027867857855342543 70888453541801786783013815)
            ·
              refine ⟨106332680312702680174520723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70888453541801786783013815 106332680312702680174520723)
              ·
                refine ⟨159499020469054020261781085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106332680312702680174520723 159499020469054020261781085)
                ·
                  refine ⟨59812132675895257598167907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159499020469054020261781085 59812132675895257598167907)
                  ·
                    refine ⟨89718199013842886397251861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59812132675895257598167907 89718199013842886397251861)
                    ·
                      refine ⟨4205540578773885299871181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89718199013842886397251861 4205540578773885299871181)
                      ·
                        rfl

theorem cell23_8190261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_8190261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190261 prefixEnd_8190261 := by exact prefixLift 8190261
  have htrace : WordTrace (prefixWord ++ tailWord_8190261) baseStart_8190261 baseEnd_8190261 := by
    simpa [prefixWord, tailWord_8190261, baseEnd_8190261] using wordTrace_append hprefix tailTrace_8190261
  have hstable : (prefixWord ++ tailWord_8190261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190261).length < 2 ^ (prefixWord ++ tailWord_8190261).sum := by decide
  have hdescent : baseEnd_8190261 < baseStart_8190261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190268 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_8190268 : Nat := 118140960795 + 8190268 * 2 ^ 59
def prefixEnd_8190268 : Nat := 4983230072969 + 3 ^ 40 * 8190268 * 2
def baseEnd_8190268 : Nat := 4205544173138466772483649

theorem tailTrace_8190268 : CollatzResearch.WordTrace tailWord_8190268 prefixEnd_8190268 4205544173138466772483649 := by
  unfold tailWord_8190268
  simp only [CollatzResearch.WordTrace]
  refine ⟨149361807546032648628217729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199149076728043531504290305 149361807546032648628217729)
  ·
    refine ⟨112021355659524486471163297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149361807546032648628217729 112021355659524486471163297)
    ·
      refine ⟨84016016744643364853372473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112021355659524486471163297 84016016744643364853372473)
      ·
        refine ⟨63012012558482523640029355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84016016744643364853372473 63012012558482523640029355)
        ·
          refine ⟨94518018837723785460044033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63012012558482523640029355 94518018837723785460044033)
          ·
            refine ⟨70888514128292839095033025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94518018837723785460044033 70888514128292839095033025)
            ·
              refine ⟨53166385596219629321274769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70888514128292839095033025 53166385596219629321274769)
              ·
                refine ⟨39874789197164721990956077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53166385596219629321274769 39874789197164721990956077)
                ·
                  refine ⟨14953045948936770746608529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39874789197164721990956077 14953045948936770746608529)
                  ·
                    refine ⟨11214784461702578059956397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14953045948936770746608529 11214784461702578059956397)
                    ·
                      refine ⟨4205544173138466772483649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11214784461702578059956397 4205544173138466772483649)
                      ·
                        rfl

theorem cell23_8190268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_8190268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190268 prefixEnd_8190268 := by exact prefixLift 8190268
  have htrace : WordTrace (prefixWord ++ tailWord_8190268) baseStart_8190268 baseEnd_8190268 := by
    simpa [prefixWord, tailWord_8190268, baseEnd_8190268] using wordTrace_append hprefix tailTrace_8190268
  have hstable : (prefixWord ++ tailWord_8190268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190268).length < 2 ^ (prefixWord ++ tailWord_8190268).sum := by decide
  have hdescent : baseEnd_8190268 < baseStart_8190268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190271 : List Nat := [1, 1, 2, 2, 4, 1, 4, 8]
def baseStart_8190271 : Nat := 118140960795 + 8190271 * 2 ^ 59
def prefixEnd_8190271 : Nat := 4983230072969 + 3 ^ 40 * 8190271 * 2
def baseEnd_8190271 : Nat := 155760952354830750398005

theorem tailTrace_8190271 : CollatzResearch.WordTrace tailWord_8190271 prefixEnd_8190271 155760952354830750398005 := by
  unfold tailWord_8190271
  simp only [CollatzResearch.WordTrace]
  refine ⟨298723724511054428768794667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199149149674036285845863111 298723724511054428768794667)
  ·
    refine ⟨448085586766581643153192001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298723724511054428768794667 448085586766581643153192001)
    ·
      refine ⟨336064190074936232364894001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448085586766581643153192001 336064190074936232364894001)
      ·
        refine ⟨252048142556202174273670501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336064190074936232364894001 252048142556202174273670501)
        ·
          refine ⟨47259026729287907676313219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252048142556202174273670501 47259026729287907676313219)
          ·
            refine ⟨70888540093931861514469829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47259026729287907676313219 70888540093931861514469829)
            ·
              refine ⟨13291601267612224033963093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70888540093931861514469829 13291601267612224033963093)
              ·
                refine ⟨155760952354830750398005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13291601267612224033963093 155760952354830750398005)
                ·
                  rfl

theorem cell23_8190271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 8].length) (baseStart_8190271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190271 prefixEnd_8190271 := by exact prefixLift 8190271
  have htrace : WordTrace (prefixWord ++ tailWord_8190271) baseStart_8190271 baseEnd_8190271 := by
    simpa [prefixWord, tailWord_8190271, baseEnd_8190271] using wordTrace_append hprefix tailTrace_8190271
  have hstable : (prefixWord ++ tailWord_8190271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190271).length < 2 ^ (prefixWord ++ tailWord_8190271).sum := by decide
  have hdescent : baseEnd_8190271 < baseStart_8190271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190275 : List Nat := [1, 1, 1, 3, 1, 3, 6, 1, 2, 4]
def baseStart_8190275 : Nat := 118140960795 + 8190275 * 2 ^ 59
def prefixEnd_8190275 : Nat := 4983230072969 + 3 ^ 40 * 8190275 * 2
def baseEnd_8190275 : Nat := 1401849255834349415032039

theorem tailTrace_8190275 : CollatzResearch.WordTrace tailWord_8190275 prefixEnd_8190275 1401849255834349415032039 := by
  unfold tailWord_8190275
  simp only [CollatzResearch.WordTrace]
  refine ⟨298723870403039937451940279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199149246935359958301293519 298723870403039937451940279)
  ·
    refine ⟨448085805604559906177910419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298723870403039937451940279 448085805604559906177910419)
    ·
      refine ⟨672128708406839859266865629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448085805604559906177910419 672128708406839859266865629)
      ·
        refine ⟨252048265652564947225074611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 672128708406839859266865629 252048265652564947225074611)
        ·
          refine ⟨378072398478847420837611917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252048265652564947225074611 378072398478847420837611917)
          ·
            refine ⟨141777149429567782814104469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378072398478847420837611917 141777149429567782814104469)
            ·
              refine ⟨6645803879510989819411147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141777149429567782814104469 6645803879510989819411147)
              ·
                refine ⟨9968705819266484729116721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6645803879510989819411147 9968705819266484729116721)
                ·
                  refine ⟨7476529364449863546837541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9968705819266484729116721 7476529364449863546837541)
                  ·
                    refine ⟨1401849255834349415032039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7476529364449863546837541 1401849255834349415032039)
                    ·
                      rfl

theorem cell23_8190275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 2, 4].length) (baseStart_8190275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190275 prefixEnd_8190275 := by exact prefixLift 8190275
  have htrace : WordTrace (prefixWord ++ tailWord_8190275) baseStart_8190275 baseEnd_8190275 := by
    simpa [prefixWord, tailWord_8190275, baseEnd_8190275] using wordTrace_append hprefix tailTrace_8190275
  have hstable : (prefixWord ++ tailWord_8190275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190275).length < 2 ^ (prefixWord ++ tailWord_8190275).sum := by decide
  have hdescent : baseEnd_8190275 < baseStart_8190275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190331 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 1, 8]
def baseStart_8190331 : Nat := 118140960795 + 8190331 * 2 ^ 59
def prefixEnd_8190331 : Nat := 4983230072969 + 3 ^ 40 * 8190331 * 2
def baseEnd_8190331 : Nat := 1401858840806566675331953

theorem tailTrace_8190331 : CollatzResearch.WordTrace tailWord_8190331 prefixEnd_8190331 1401858840806566675331953 := by
  unfold tailWord_8190331
  simp only [CollatzResearch.WordTrace]
  refine ⟨298725912890837059015978847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199150608593891372677319231 298725912890837059015978847)
  ·
    refine ⟨448088869336255588523968271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298725912890837059015978847 448088869336255588523968271)
    ·
      refine ⟨672133304004383382785952407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448088869336255588523968271 672133304004383382785952407)
      ·
        refine ⟨1008199956006575074178928611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672133304004383382785952407 1008199956006575074178928611)
        ·
          refine ⟨1512299934009862611268392917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008199956006575074178928611 1512299934009862611268392917)
          ·
            refine ⟨35444529703356154951602959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1512299934009862611268392917 35444529703356154951602959)
            ·
              refine ⟨53166794555034232427404439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35444529703356154951602959 53166794555034232427404439)
              ·
                refine ⟨79750191832551348641106659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53166794555034232427404439 79750191832551348641106659)
                ·
                  refine ⟨119625287748827022961659989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79750191832551348641106659 119625287748827022961659989)
                  ·
                    refine ⟨1401858840806566675331953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119625287748827022961659989 1401858840806566675331953)
                    ·
                      rfl

theorem cell23_8190331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 8].length) (baseStart_8190331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190331 prefixEnd_8190331 := by exact prefixLift 8190331
  have htrace : WordTrace (prefixWord ++ tailWord_8190331) baseStart_8190331 baseEnd_8190331 := by
    simpa [prefixWord, tailWord_8190331, baseEnd_8190331] using wordTrace_append hprefix tailTrace_8190331
  have hstable : (prefixWord ++ tailWord_8190331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190331).length < 2 ^ (prefixWord ++ tailWord_8190331).sum := by decide
  have hdescent : baseEnd_8190331 < baseStart_8190331 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190361 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 9]
def baseStart_8190361 : Nat := 118140960795 + 8190361 * 2 ^ 59
def prefixEnd_8190361 : Nat := 4983230072969 + 3 ^ 40 * 8190361 * 2
def baseEnd_8190361 : Nat := 467287991871037212068969

theorem tailTrace_8190361 : CollatzResearch.WordTrace tailWord_8190361 prefixEnd_8190361 467287991871037212068969 := by
  unfold tailWord_8190361
  simp only [CollatzResearch.WordTrace]
  refine ⟨298727007080728374139570937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199151338053818916093047291 298727007080728374139570937)
  ·
    refine ⟨224045255310546280604678203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298727007080728374139570937 224045255310546280604678203)
    ·
      refine ⟨336067882965819420907017305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224045255310546280604678203 336067882965819420907017305)
      ·
        refine ⟨252050912224364565680262979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336067882965819420907017305 252050912224364565680262979)
        ·
          refine ⟨378076368336546848520394469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252050912224364565680262979 378076368336546848520394469)
          ·
            refine ⟨70889319063102534097573963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378076368336546848520394469 70889319063102534097573963)
            ·
              refine ⟨106333978594653801146360945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70889319063102534097573963 106333978594653801146360945)
              ·
                refine ⟨79750483945990350859770709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106333978594653801146360945 79750483945990350859770709)
                ·
                  refine ⟨467287991871037212068969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79750483945990350859770709 467287991871037212068969)
                  ·
                    rfl

theorem cell23_8190361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 9].length) (baseStart_8190361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190361 prefixEnd_8190361 := by exact prefixLift 8190361
  have htrace : WordTrace (prefixWord ++ tailWord_8190361) baseStart_8190361 baseEnd_8190361 := by
    simpa [prefixWord, tailWord_8190361, baseEnd_8190361] using wordTrace_append hprefix tailTrace_8190361
  have hstable : (prefixWord ++ tailWord_8190361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190361).length < 2 ^ (prefixWord ++ tailWord_8190361).sum := by decide
  have hdescent : baseEnd_8190361 < baseStart_8190361 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190366 : List Nat := [4, 3, 1, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_8190366 : Nat := 118140960795 + 8190366 * 2 ^ 59
def prefixEnd_8190366 : Nat := 4983230072969 + 3 ^ 40 * 8190366 * 2
def baseEnd_8190366 : Nat := 4205594494242607389058199

theorem tailTrace_8190366 : CollatzResearch.WordTrace tailWord_8190366 prefixEnd_8190366 4205594494242607389058199 := by
  unfold tailWord_8190366
  simp only [CollatzResearch.WordTrace]
  refine ⟨37340898680713782499187869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199151459630473506662335301 37340898680713782499187869)
  ·
    refine ⟨14002837005267668437195451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37340898680713782499187869 14002837005267668437195451)
    ·
      refine ⟨21004255507901502655793177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14002837005267668437195451 21004255507901502655793177)
      ·
        refine ⟨15753191630926126991844883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21004255507901502655793177 15753191630926126991844883)
        ·
          refine ⟨23629787446389190487767325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15753191630926126991844883 23629787446389190487767325)
          ·
            refine ⟨8861170292395946432912747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23629787446389190487767325 8861170292395946432912747)
            ·
              refine ⟨13291755438593919649369121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8861170292395946432912747 13291755438593919649369121)
              ·
                refine ⟨9968816578945439737026841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13291755438593919649369121 9968816578945439737026841)
                ·
                  refine ⟨7476612434209079802770131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9968816578945439737026841 7476612434209079802770131)
                  ·
                    refine ⟨11214918651313619704155197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7476612434209079802770131 11214918651313619704155197)
                    ·
                      refine ⟨4205594494242607389058199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11214918651313619704155197 4205594494242607389058199)
                      ·
                        rfl

theorem cell23_8190366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_8190366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190366 prefixEnd_8190366 := by exact prefixLift 8190366
  have htrace : WordTrace (prefixWord ++ tailWord_8190366) baseStart_8190366 baseEnd_8190366 := by
    simpa [prefixWord, tailWord_8190366, baseEnd_8190366] using wordTrace_append hprefix tailTrace_8190366
  have hstable : (prefixWord ++ tailWord_8190366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190366).length < 2 ^ (prefixWord ++ tailWord_8190366).sum := by decide
  have hdescent : baseEnd_8190366 < baseStart_8190366 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190368 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 4]
def baseStart_8190368 : Nat := 118140960795 + 8190368 * 2 ^ 59
def prefixEnd_8190368 : Nat := 4983230072969 + 3 ^ 40 * 8190368 * 2
def baseEnd_8190368 : Nat := 4205595521203916381233189

theorem tailTrace_8190368 : CollatzResearch.WordTrace tailWord_8190368 prefixEnd_8190368 4205595521203916381233189 := by
  unfold tailWord_8190368
  simp only [CollatzResearch.WordTrace]
  refine ⟨149363631195851507167537879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199151508261135342890050505 149363631195851507167537879)
  ·
    refine ⟨224045446793777260751306819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149363631195851507167537879 224045446793777260751306819)
    ·
      refine ⟨336068170190665891126960229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224045446793777260751306819 336068170190665891126960229)
      ·
        refine ⟨63012781910749854586305043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336068170190665891126960229 63012781910749854586305043)
        ·
          refine ⟨94519172866124781879457565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63012781910749854586305043 94519172866124781879457565)
          ·
            refine ⟨35444689824796793204796587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94519172866124781879457565 35444689824796793204796587)
            ·
              refine ⟨53167034737195189807194881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35444689824796793204796587 53167034737195189807194881)
              ·
                refine ⟨39875276052896392355396161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53167034737195189807194881 39875276052896392355396161)
                ·
                  refine ⟨29906457039672294266547121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39875276052896392355396161 29906457039672294266547121)
                  ·
                    refine ⟨22429842779754220699910341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29906457039672294266547121 22429842779754220699910341)
                    ·
                      refine ⟨4205595521203916381233189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22429842779754220699910341 4205595521203916381233189)
                      ·
                        rfl

theorem cell23_8190368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_8190368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190368 prefixEnd_8190368 := by exact prefixLift 8190368
  have htrace : WordTrace (prefixWord ++ tailWord_8190368) baseStart_8190368 baseEnd_8190368 := by
    simpa [prefixWord, tailWord_8190368, baseEnd_8190368] using wordTrace_append hprefix tailTrace_8190368
  have hstable : (prefixWord ++ tailWord_8190368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190368).length < 2 ^ (prefixWord ++ tailWord_8190368).sum := by decide
  have hdescent : baseEnd_8190368 < baseStart_8190368 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190389 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_8190389 : Nat := 118140960795 + 8190389 * 2 ^ 59
def prefixEnd_8190389 : Nat := 4983230072969 + 3 ^ 40 * 8190389 * 2
def baseEnd_8190389 : Nat := 4205606304297660799070593

theorem tailTrace_8190389 : CollatzResearch.WordTrace tailWord_8190389 prefixEnd_8190389 4205606304297660799070593 := by
  unfold tailWord_8190389
  simp only [CollatzResearch.WordTrace]
  refine ⟨298728028324626934921590221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199152018883084623281060147 298728028324626934921590221)
  ·
    refine ⟨112023010621735100595596333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298728028324626934921590221 112023010621735100595596333)
    ·
      refine ⟨42008628983150662723348625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112023010621735100595596333 42008628983150662723348625)
      ·
        refine ⟨31506471737362997042511469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42008628983150662723348625 31506471737362997042511469)
        ·
          refine ⟨11814926901511123890941801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31506471737362997042511469 11814926901511123890941801)
          ·
            refine ⟨8861195176133342918206351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11814926901511123890941801 8861195176133342918206351)
            ·
              refine ⟨13291792764200014377309527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8861195176133342918206351 13291792764200014377309527)
              ·
                refine ⟨19937689146300021565964291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13291792764200014377309527 19937689146300021565964291)
                ·
                  refine ⟨29906533719450032348946437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19937689146300021565964291 29906533719450032348946437)
                  ·
                    refine ⟨5607475072396881065427457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29906533719450032348946437 5607475072396881065427457)
                    ·
                      refine ⟨4205606304297660799070593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5607475072396881065427457 4205606304297660799070593)
                      ·
                        rfl

theorem cell23_8190389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_8190389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190389 prefixEnd_8190389 := by exact prefixLift 8190389
  have htrace : WordTrace (prefixWord ++ tailWord_8190389) baseStart_8190389 baseEnd_8190389 := by
    simpa [prefixWord, tailWord_8190389, baseEnd_8190389] using wordTrace_append hprefix tailTrace_8190389
  have hstable : (prefixWord ++ tailWord_8190389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190389).length < 2 ^ (prefixWord ++ tailWord_8190389).sum := by decide
  have hdescent : baseEnd_8190389 < baseStart_8190389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190408 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 1, 7]
def baseStart_8190408 : Nat := 118140960795 + 8190408 * 2 ^ 59
def prefixEnd_8190408 : Nat := 4983230072969 + 3 ^ 40 * 8190408 * 2
def baseEnd_8190408 : Nat := 1401872020143365408244335

theorem tailTrace_8190408 : CollatzResearch.WordTrace tailWord_8190408 prefixEnd_8190408 1401872020143365408244335 := by
  unfold tailWord_8190408
  simp only [CollatzResearch.WordTrace]
  refine ⟨149364360655779050583265939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199152480874372067444354585 149364360655779050583265939)
  ·
    refine ⟨224046540983668575874898909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149364360655779050583265939 224046540983668575874898909)
    ·
      refine ⟨84017452868875715953087091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224046540983668575874898909 84017452868875715953087091)
      ·
        refine ⟨126026179303313573929630637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84017452868875715953087091 126026179303313573929630637)
        ·
          refine ⟨47259817238742590223611489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126026179303313573929630637 47259817238742590223611489)
          ·
            refine ⟨35444862929056942667708617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47259817238742590223611489 35444862929056942667708617)
            ·
              refine ⟨26583647196792707000781463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35444862929056942667708617 26583647196792707000781463)
              ·
                refine ⟨39875470795189060501172195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26583647196792707000781463 39875470795189060501172195)
                ·
                  refine ⟨59813206192783590751758293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39875470795189060501172195 59813206192783590751758293)
                  ·
                    refine ⟨1401872020143365408244335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59813206192783590751758293 1401872020143365408244335)
                    ·
                      rfl

theorem cell23_8190408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_8190408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190408 prefixEnd_8190408 := by exact prefixLift 8190408
  have htrace : WordTrace (prefixWord ++ tailWord_8190408) baseStart_8190408 baseEnd_8190408 := by
    simpa [prefixWord, tailWord_8190408, baseEnd_8190408] using wordTrace_append hprefix tailTrace_8190408
  have hstable : (prefixWord ++ tailWord_8190408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190408).length < 2 ^ (prefixWord ++ tailWord_8190408).sum := by decide
  have hdescent : baseEnd_8190408 < baseStart_8190408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190435 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 5]
def baseStart_8190435 : Nat := 118140960795 + 8190435 * 2 ^ 59
def prefixEnd_8190435 : Nat := 4983230072969 + 3 ^ 40 * 8190435 * 2
def baseEnd_8190435 : Nat := 4205629924407767619095381

theorem tailTrace_8190435 : CollatzResearch.WordTrace tailWord_8190435 prefixEnd_8190435 4205629924407767619095381 := by
  unfold tailWord_8190435
  simp only [CollatzResearch.WordTrace]
  refine ⟨298729706082460284777764759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199153137388306856518509839 298729706082460284777764759)
  ·
    refine ⟨448094559123690427166647139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298729706082460284777764759 448094559123690427166647139)
    ·
      refine ⟨672141838685535640749970709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448094559123690427166647139 672141838685535640749970709)
      ·
        refine ⟨31506648688384483160154877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 672141838685535640749970709 31506648688384483160154877)
        ·
          refine ⟨11814993258144181185058079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31506648688384483160154877 11814993258144181185058079)
          ·
            refine ⟨17722489887216271777587119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11814993258144181185058079 17722489887216271777587119)
            ·
              refine ⟨26583734830824407666380679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17722489887216271777587119 26583734830824407666380679)
              ·
                refine ⟨39875602246236611499571019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26583734830824407666380679 39875602246236611499571019)
                ·
                  refine ⟨59813403369354917249356529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39875602246236611499571019 59813403369354917249356529)
                  ·
                    refine ⟨44860052527016187937017397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59813403369354917249356529 44860052527016187937017397)
                    ·
                      refine ⟨4205629924407767619095381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44860052527016187937017397 4205629924407767619095381)
                      ·
                        rfl

theorem cell23_8190435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_8190435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190435 prefixEnd_8190435 := by exact prefixLift 8190435
  have htrace : WordTrace (prefixWord ++ tailWord_8190435) baseStart_8190435 baseEnd_8190435 := by
    simpa [prefixWord, tailWord_8190435, baseEnd_8190435] using wordTrace_append hprefix tailTrace_8190435
  have hstable : (prefixWord ++ tailWord_8190435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190435).length < 2 ^ (prefixWord ++ tailWord_8190435).sum := by decide
  have hdescent : baseEnd_8190435 < baseStart_8190435 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190472 : List Nat := [2, 1, 3, 2, 1, 1, 1, 7, 1, 4]
def baseStart_8190472 : Nat := 118140960795 + 8190472 * 2 ^ 59
def prefixEnd_8190472 : Nat := 4983230072969 + 3 ^ 40 * 8190472 * 2
def baseEnd_8190472 : Nat := 1401882974397327991444237

theorem tailTrace_8190472 : CollatzResearch.WordTrace tailWord_8190472 prefixEnd_8190472 1401882974397327991444237 := by
  unfold tailWord_8190472
  simp only [CollatzResearch.WordTrace]
  refine ⟨149365527791663120048430835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199154037055550826731241113 149365527791663120048430835)
  ·
    refine ⟨224048291687494680072646253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149365527791663120048430835 224048291687494680072646253)
    ·
      refine ⟨84018109382810505027242345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224048291687494680072646253 84018109382810505027242345)
      ·
        refine ⟨63013582037107878770431759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84018109382810505027242345 63013582037107878770431759)
        ·
          refine ⟨94520373055661818155647639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63013582037107878770431759 94520373055661818155647639)
          ·
            refine ⟨141780559583492727233471459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94520373055661818155647639 141780559583492727233471459)
            ·
              refine ⟨212670839375239090850207189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141780559583492727233471459 212670839375239090850207189)
              ·
                refine ⟨4984472797857166191801731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 212670839375239090850207189 4984472797857166191801731)
                ·
                  refine ⟨7476709196785749287702597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4984472797857166191801731 7476709196785749287702597)
                  ·
                    refine ⟨1401882974397327991444237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7476709196785749287702597 1401882974397327991444237)
                    ·
                      rfl

theorem cell23_8190472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_8190472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190472 prefixEnd_8190472 := by exact prefixLift 8190472
  have htrace : WordTrace (prefixWord ++ tailWord_8190472) baseStart_8190472 baseEnd_8190472 := by
    simpa [prefixWord, tailWord_8190472, baseEnd_8190472] using wordTrace_append hprefix tailTrace_8190472
  have hstable : (prefixWord ++ tailWord_8190472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190472).length < 2 ^ (prefixWord ++ tailWord_8190472).sum := by decide
  have hdescent : baseEnd_8190472 < baseStart_8190472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190485 : List Nat := [1, 3, 2, 1, 3, 1, 4, 2, 6]
def baseStart_8190485 : Nat := 118140960795 + 8190485 * 2 ^ 59
def prefixEnd_8190485 : Nat := 4983230072969 + 3 ^ 40 * 8190485 * 2
def baseEnd_8190485 : Nat := 467295066493388047052239

theorem tailTrace_8190485 : CollatzResearch.WordTrace tailWord_8190485 prefixEnd_8190485 467295066493388047052239 := by
  unfold tailWord_8190485
  simp only [CollatzResearch.WordTrace]
  refine ⟨298731529732279143317084909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199154353154852762211389939 298731529732279143317084909)
  ·
    refine ⟨112024323649604678743906841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298731529732279143317084909 112024323649604678743906841)
    ·
      refine ⟨84018242737203509057930131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112024323649604678743906841 84018242737203509057930131)
      ·
        refine ⟨126027364105805263586895197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84018242737203509057930131 126027364105805263586895197)
        ·
          refine ⟨47260261539676973845085699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126027364105805263586895197 47260261539676973845085699)
          ·
            refine ⟨70890392309515460767628549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47260261539676973845085699 70890392309515460767628549)
            ·
              refine ⟨13291948558034148893930353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70890392309515460767628549 13291948558034148893930353)
              ·
                refine ⟨9968961418525611670447765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13291948558034148893930353 9968961418525611670447765)
                ·
                  refine ⟨467295066493388047052239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9968961418525611670447765 467295066493388047052239)
                  ·
                    rfl

theorem cell23_8190485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_8190485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190485 prefixEnd_8190485 := by exact prefixLift 8190485
  have htrace : WordTrace (prefixWord ++ tailWord_8190485) baseStart_8190485 baseEnd_8190485 := by
    simpa [prefixWord, tailWord_8190485, baseEnd_8190485] using wordTrace_append hprefix tailTrace_8190485
  have hstable : (prefixWord ++ tailWord_8190485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190485).length < 2 ^ (prefixWord ++ tailWord_8190485).sum := by decide
  have hdescent : baseEnd_8190485 < baseStart_8190485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190515 : List Nat := [1, 1, 1, 2, 4, 2, 2, 4, 1, 5]
def baseStart_8190515 : Nat := 118140960795 + 8190515 * 2 ^ 59
def prefixEnd_8190515 : Nat := 4983230072969 + 3 ^ 40 * 8190515 * 2
def baseEnd_8190515 : Nat := 1401890334286709102031671

theorem tailTrace_8190515 : CollatzResearch.WordTrace tailWord_8190515 prefixEnd_8190515 1401890334286709102031671 := by
  unfold tailWord_8190515
  simp only [CollatzResearch.WordTrace]
  refine ⟨298732623922170458440676999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199155082614780305627117999 298732623922170458440676999)
  ·
    refine ⟨448098935883255687661015499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298732623922170458440676999 448098935883255687661015499)
    ·
      refine ⟨672148403824883531491523249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448098935883255687661015499 672148403824883531491523249)
      ·
        refine ⟨504111302868662648618642437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672148403824883531491523249 504111302868662648618642437)
        ·
          refine ⟨94520869287874246615995457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 504111302868662648618642437 94520869287874246615995457)
          ·
            refine ⟨70890651965905684961996593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94520869287874246615995457 70890651965905684961996593)
            ·
              refine ⟨53167988974429263721497445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70890651965905684961996593 53167988974429263721497445)
              ·
                refine ⟨9968997932705486947780771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53167988974429263721497445 9968997932705486947780771)
                ·
                  refine ⟨14953496899058230421671157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9968997932705486947780771 14953496899058230421671157)
                  ·
                    refine ⟨1401890334286709102031671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14953496899058230421671157 1401890334286709102031671)
                    ·
                      rfl

theorem cell23_8190515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 5].length) (baseStart_8190515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190515 prefixEnd_8190515 := by exact prefixLift 8190515
  have htrace : WordTrace (prefixWord ++ tailWord_8190515) baseStart_8190515 baseEnd_8190515 := by
    simpa [prefixWord, tailWord_8190515, baseEnd_8190515] using wordTrace_append hprefix tailTrace_8190515
  have hstable : (prefixWord ++ tailWord_8190515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190515).length < 2 ^ (prefixWord ++ tailWord_8190515).sum := by decide
  have hdescent : baseEnd_8190515 < baseStart_8190515 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190522 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2]
def baseStart_8190522 : Nat := 118140960795 + 8190522 * 2 ^ 59
def prefixEnd_8190522 : Nat := 4983230072969 + 3 ^ 40 * 8190522 * 2
def baseEnd_8190522 : Nat := 4205674597224708778707481

theorem tailTrace_8190522 : CollatzResearch.WordTrace tailWord_8190522 prefixEnd_8190522 4205674597224708778707481 := by
  unfold tailWord_8190522
  simp only [CollatzResearch.WordTrace]
  refine ⟨74683219808286274659045455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199155252822096732424121213 74683219808286274659045455)
  ·
    refine ⟨112024829712429411988568183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74683219808286274659045455 112024829712429411988568183)
    ·
      refine ⟨168037244568644117982852275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112024829712429411988568183 168037244568644117982852275)
      ·
        refine ⟨252055866852966176974278413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168037244568644117982852275 252055866852966176974278413)
        ·
          refine ⟨94520950069862316365354405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252055866852966176974278413 94520950069862316365354405)
          ·
            refine ⟨17722678138099184318503951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94520950069862316365354405 17722678138099184318503951)
            ·
              refine ⟨26584017207148776477755927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17722678138099184318503951 26584017207148776477755927)
              ·
                refine ⟨39876025810723164716633891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26584017207148776477755927 39876025810723164716633891)
                ·
                  refine ⟨59814038716084747074950837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39876025810723164716633891 59814038716084747074950837)
                  ·
                    refine ⟨5607566129632945038276641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59814038716084747074950837 5607566129632945038276641)
                    ·
                      refine ⟨4205674597224708778707481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5607566129632945038276641 4205674597224708778707481)
                      ·
                        rfl

theorem cell23_8190522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2].length) (baseStart_8190522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190522 prefixEnd_8190522 := by exact prefixLift 8190522
  have htrace : WordTrace (prefixWord ++ tailWord_8190522) baseStart_8190522 baseEnd_8190522 := by
    simpa [prefixWord, tailWord_8190522, baseEnd_8190522] using wordTrace_append hprefix tailTrace_8190522
  have hstable : (prefixWord ++ tailWord_8190522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190522).length < 2 ^ (prefixWord ++ tailWord_8190522).sum := by decide
  have hdescent : baseEnd_8190522 < baseStart_8190522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190572 : List Nat := [2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 3]
def baseStart_8190572 : Nat := 118140960795 + 8190572 * 2 ^ 59
def prefixEnd_8190572 : Nat := 4983230072969 + 3 ^ 40 * 8190572 * 2
def baseEnd_8190572 : Nat := 4205700271257433583082251

theorem tailTrace_8190572 : CollatzResearch.WordTrace tailWord_8190572 prefixEnd_8190572 4205700271257433583082251 := by
  unfold tailWord_8190572
  simp only [CollatzResearch.WordTrace]
  refine ⟨149367351441481978587750985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199156468588642638117001313 149367351441481978587750985)
  ·
    refine ⟨112025513581111483940813239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149367351441481978587750985 112025513581111483940813239)
    ·
      refine ⟨168038270371667225911219859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112025513581111483940813239 168038270371667225911219859)
      ·
        refine ⟨252057405557500838866829789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168038270371667225911219859 252057405557500838866829789)
        ·
          refine ⟨94521527084062814575061171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252057405557500838866829789 94521527084062814575061171)
          ·
            refine ⟨141782290626094221862591757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94521527084062814575061171 141782290626094221862591757)
            ·
              refine ⟨53168358984785333198471909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141782290626094221862591757 53168358984785333198471909)
              ·
                refine ⟨9969067309647249974713483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53168358984785333198471909 9969067309647249974713483)
                ·
                  refine ⟨14953600964470874962070225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9969067309647249974713483 14953600964470874962070225)
                  ·
                    refine ⟨11215200723353156221552669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14953600964470874962070225 11215200723353156221552669)
                    ·
                      refine ⟨4205700271257433583082251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11215200723353156221552669 4205700271257433583082251)
                      ·
                        rfl

theorem cell23_8190572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_8190572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190572 prefixEnd_8190572 := by exact prefixLift 8190572
  have htrace : WordTrace (prefixWord ++ tailWord_8190572) baseStart_8190572 baseEnd_8190572 := by
    simpa [prefixWord, tailWord_8190572, baseEnd_8190572] using wordTrace_append hprefix tailTrace_8190572
  have hstable : (prefixWord ++ tailWord_8190572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190572).length < 2 ^ (prefixWord ++ tailWord_8190572).sum := by decide
  have hdescent : baseEnd_8190572 < baseStart_8190572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190575 : List Nat := [1, 1, 2, 1, 3, 2, 6, 7]
def baseStart_8190575 : Nat := 118140960795 + 8190575 * 2 ^ 59
def prefixEnd_8190575 : Nat := 4983230072969 + 3 ^ 40 * 8190575 * 2
def baseEnd_8190575 : Nat := 155766733766644335975731

theorem tailTrace_8190575 : CollatzResearch.WordTrace tailWord_8190575 prefixEnd_8190575 155766733766644335975731 := by
  unfold tailWord_8190575
  simp only [CollatzResearch.WordTrace]
  refine ⟨298734812301953088687861179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199156541534635392458574119 298734812301953088687861179)
  ·
    refine ⟨448102218452929633031791769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298734812301953088687861179 448102218452929633031791769)
    ·
      refine ⟨336076663839697224773843827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448102218452929633031791769 336076663839697224773843827)
      ·
        refine ⟨504114995759545837160765741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336076663839697224773843827 504114995759545837160765741)
        ·
          refine ⟨189043123409829688935287153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504114995759545837160765741 189043123409829688935287153)
          ·
            refine ⟨141782342557372266701465365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189043123409829688935287153 141782342557372266701465365)
            ·
              refine ⟨6646047307376825001631189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141782342557372266701465365 6646047307376825001631189)
              ·
                refine ⟨155766733766644335975731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6646047307376825001631189 155766733766644335975731)
                ·
                  rfl

theorem cell23_8190575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 7].length) (baseStart_8190575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190575 prefixEnd_8190575 := by exact prefixLift 8190575
  have htrace : WordTrace (prefixWord ++ tailWord_8190575) baseStart_8190575 baseEnd_8190575 := by
    simpa [prefixWord, tailWord_8190575, baseEnd_8190575] using wordTrace_append hprefix tailTrace_8190575
  have hstable : (prefixWord ++ tailWord_8190575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190575).length < 2 ^ (prefixWord ++ tailWord_8190575).sum := by decide
  have hdescent : baseEnd_8190575 < baseStart_8190575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190745 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 6]
def baseStart_8190745 : Nat := 118140960795 + 8190745 * 2 ^ 59
def prefixEnd_8190745 : Nat := 4983230072969 + 3 ^ 40 * 8190745 * 2
def baseEnd_8190745 : Nat := 4205789103410661406218955

theorem tailTrace_8190745 : CollatzResearch.WordTrace tailWord_8190745 prefixEnd_8190745 4205789103410661406218955 := by
  unfold tailWord_8190745
  simp only [CollatzResearch.WordTrace]
  refine ⟨298741012711337207721549689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199160675140891471814366459 298741012711337207721549689)
  ·
    refine ⟨224055759533502905791162267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298741012711337207721549689 224055759533502905791162267)
    ·
      refine ⟨336083639300254358686743401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224055759533502905791162267 336083639300254358686743401)
      ·
        refine ⟨252062729475190769015057551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336083639300254358686743401 252062729475190769015057551)
        ·
          refine ⟨378094094212786153522586327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252062729475190769015057551 378094094212786153522586327)
          ·
            refine ⟨567141141319179230283879491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378094094212786153522586327 567141141319179230283879491)
            ·
              refine ⟨850711711978768845425819237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567141141319179230283879491 850711711978768845425819237)
              ·
                refine ⟨159508445996019158517341107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 850711711978768845425819237 159508445996019158517341107)
                ·
                  refine ⟨239262668994028737776011661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159508445996019158517341107 239262668994028737776011661)
                  ·
                    refine ⟨89723500872760776666004373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239262668994028737776011661 89723500872760776666004373)
                    ·
                      refine ⟨4205789103410661406218955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89723500872760776666004373 4205789103410661406218955)
                      ·
                        rfl

theorem cell23_8190745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_8190745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190745 prefixEnd_8190745 := by exact prefixLift 8190745
  have htrace : WordTrace (prefixWord ++ tailWord_8190745) baseStart_8190745 baseEnd_8190745 := by
    simpa [prefixWord, tailWord_8190745, baseEnd_8190745] using wordTrace_append hprefix tailTrace_8190745
  have hstable : (prefixWord ++ tailWord_8190745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190745).length < 2 ^ (prefixWord ++ tailWord_8190745).sum := by decide
  have hdescent : baseEnd_8190745 < baseStart_8190745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190766 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_8190766 : Nat := 118140960795 + 8190766 * 2 ^ 59
def prefixEnd_8190766 : Nat := 4983230072969 + 3 ^ 40 * 8190766 * 2
def baseEnd_8190766 : Nat := 4205799886504405824056359

theorem tailTrace_8190766 : CollatzResearch.WordTrace tailWord_8190766 prefixEnd_8190766 4205799886504405824056359 := by
  unfold tailWord_8190766
  simp only [CollatzResearch.WordTrace]
  refine ⟨37342722330532641038508019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199161185762840752205376101 37342722330532641038508019)
  ·
    refine ⟨56014083495798961557762029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37342722330532641038508019 56014083495798961557762029)
    ·
      refine ⟨21005281310924610584160761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56014083495798961557762029 21005281310924610584160761)
      ·
        refine ⟨15753960983193457938120571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21005281310924610584160761 15753960983193457938120571)
        ·
          refine ⟨23630941474790186907180857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15753960983193457938120571 23630941474790186907180857)
          ·
            refine ⟨17723206106092640180385643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23630941474790186907180857 17723206106092640180385643)
            ·
              refine ⟨26584809159138960270578465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17723206106092640180385643 26584809159138960270578465)
              ·
                refine ⟨19938606869354220202933849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26584809159138960270578465 19938606869354220202933849)
                ·
                  refine ⟨14953955152015665152200387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19938606869354220202933849 14953955152015665152200387)
                  ·
                    refine ⟨22430932728023497728300581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14953955152015665152200387 22430932728023497728300581)
                    ·
                      refine ⟨4205799886504405824056359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22430932728023497728300581 4205799886504405824056359)
                      ·
                        rfl

theorem cell23_8190766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_8190766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190766 prefixEnd_8190766 := by exact prefixLift 8190766
  have htrace : WordTrace (prefixWord ++ tailWord_8190766) baseStart_8190766 baseEnd_8190766 := by
    simpa [prefixWord, tailWord_8190766, baseEnd_8190766] using wordTrace_append hprefix tailTrace_8190766
  have hstable : (prefixWord ++ tailWord_8190766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190766).length < 2 ^ (prefixWord ++ tailWord_8190766).sum := by decide
  have hdescent : baseEnd_8190766 < baseStart_8190766 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190769 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 2, 2, 3]
def baseStart_8190769 : Nat := 118140960795 + 8190769 * 2 ^ 59
def prefixEnd_8190769 : Nat := 4983230072969 + 3 ^ 40 * 8190769 * 2
def baseEnd_8190769 : Nat := 4205801426946369312318845

theorem tailTrace_8190769 : CollatzResearch.WordTrace tailWord_8190769 prefixEnd_8190769 4205801426946369312318845 := by
  unfold tailWord_8190769
  simp only [CollatzResearch.WordTrace]
  refine ⟨298741888063250259820423361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199161258708833506546948907 298741888063250259820423361)
  ·
    refine ⟨224056416047437694865317521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298741888063250259820423361 224056416047437694865317521)
    ·
      refine ⟨168042312035578271148988141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224056416047437694865317521 168042312035578271148988141)
      ·
        refine ⟨63015867013341851680870553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168042312035578271148988141 63015867013341851680870553)
        ·
          refine ⟨47261900260006388760652915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63015867013341851680870553 47261900260006388760652915)
          ·
            refine ⟨70892850390009583140979373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47261900260006388760652915 70892850390009583140979373)
            ·
              refine ⟨26584818896253593677867265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70892850390009583140979373 26584818896253593677867265)
              ·
                refine ⟨19938614172190195258400449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26584818896253593677867265 19938614172190195258400449)
                ·
                  refine ⟨14953960629142646443800337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19938614172190195258400449 14953960629142646443800337)
                  ·
                    refine ⟨11215470471856984832850253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14953960629142646443800337 11215470471856984832850253)
                    ·
                      refine ⟨4205801426946369312318845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11215470471856984832850253 4205801426946369312318845)
                      ·
                        rfl

theorem cell23_8190769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_8190769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190769 prefixEnd_8190769 := by exact prefixLift 8190769
  have htrace : WordTrace (prefixWord ++ tailWord_8190769) baseStart_8190769 baseEnd_8190769 := by
    simpa [prefixWord, tailWord_8190769, baseEnd_8190769] using wordTrace_append hprefix tailTrace_8190769
  have hstable : (prefixWord ++ tailWord_8190769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190769).length < 2 ^ (prefixWord ++ tailWord_8190769).sum := by decide
  have hdescent : baseEnd_8190769 < baseStart_8190769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190833 : List Nat := [1, 2, 2, 2, 1, 5, 1, 4, 1, 1, 3]
def baseStart_8190833 : Nat := 118140960795 + 8190833 * 2 ^ 59
def prefixEnd_8190833 : Nat := 4983230072969 + 3 ^ 40 * 8190833 * 2
def baseEnd_8190833 : Nat := 4205834289708257061918551

theorem tailTrace_8190833 : CollatzResearch.WordTrace tailWord_8190833 prefixEnd_8190833 4205834289708257061918551 := by
  unfold tailWord_8190833
  simp only [CollatzResearch.WordTrace]
  refine ⟨298744222335018398750753153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199162814890012265833835435 298744222335018398750753153)
  ·
    refine ⟨224058166751263799063064865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298744222335018398750753153 224058166751263799063064865)
    ·
      refine ⟨168043625063447849297298649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224058166751263799063064865 168043625063447849297298649)
      ·
        refine ⟨126032718797585886972973987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168043625063447849297298649 126032718797585886972973987)
        ·
          refine ⟨189049078196378830459460981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126032718797585886972973987 189049078196378830459460981)
          ·
            refine ⟨17723351080910515355574467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189049078196378830459460981 17723351080910515355574467)
            ·
              refine ⟨26585026621365773033361701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17723351080910515355574467 26585026621365773033361701)
              ·
                refine ⟨4984692491506082443755319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26585026621365773033361701 4984692491506082443755319)
                ·
                  refine ⟨7477038737259123665632979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4984692491506082443755319 7477038737259123665632979)
                  ·
                    refine ⟨11215558105888685498449469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7477038737259123665632979 11215558105888685498449469)
                    ·
                      refine ⟨4205834289708257061918551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11215558105888685498449469 4205834289708257061918551)
                      ·
                        rfl

theorem cell23_8190833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_8190833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190833 prefixEnd_8190833 := by exact prefixLift 8190833
  have htrace : WordTrace (prefixWord ++ tailWord_8190833) baseStart_8190833 baseEnd_8190833 := by
    simpa [prefixWord, tailWord_8190833, baseEnd_8190833] using wordTrace_append hprefix tailTrace_8190833
  have hstable : (prefixWord ++ tailWord_8190833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190833).length < 2 ^ (prefixWord ++ tailWord_8190833).sum := by decide
  have hdescent : baseEnd_8190833 < baseStart_8190833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190842 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_8190842 : Nat := 118140960795 + 8190842 * 2 ^ 59
def prefixEnd_8190842 : Nat := 4983230072969 + 3 ^ 40 * 8190842 * 2
def baseEnd_8190842 : Nat := 4205838911034147526706009

theorem tailTrace_8190842 : CollatzResearch.WordTrace tailWord_8190842 prefixEnd_8190842 4205838911034147526706009 := by
  unfold tailWord_8190842
  simp only [CollatzResearch.WordTrace]
  refine ⟨74686137647996448321957695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199163033727990528858553853 74686137647996448321957695)
  ·
    refine ⟨112029206471994672482936543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74686137647996448321957695 112029206471994672482936543)
    ·
      refine ⟨168043809707992008724404815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112029206471994672482936543 168043809707992008724404815)
      ·
        refine ⟨252065714561988013086607223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168043809707992008724404815 252065714561988013086607223)
        ·
          refine ⟨378098571842982019629910835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252065714561988013086607223 378098571842982019629910835)
          ·
            refine ⟨567147857764473029444866253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378098571842982019629910835 567147857764473029444866253)
            ·
              refine ⟨212680446661677386041824845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 567147857764473029444866253 212680446661677386041824845)
              ·
                refine ⟨79755167498129019765684317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212680446661677386041824845 79755167498129019765684317)
                ·
                  refine ⟨29908187811798382412131619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79755167498129019765684317 29908187811798382412131619)
                  ·
                    refine ⟨44862281717697573618197429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29908187811798382412131619 44862281717697573618197429)
                    ·
                      refine ⟨4205838911034147526706009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44862281717697573618197429 4205838911034147526706009)
                      ·
                        rfl

theorem cell23_8190842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_8190842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190842 prefixEnd_8190842 := by exact prefixLift 8190842
  have htrace : WordTrace (prefixWord ++ tailWord_8190842) baseStart_8190842 baseEnd_8190842 := by
    simpa [prefixWord, tailWord_8190842, baseEnd_8190842] using wordTrace_append hprefix tailTrace_8190842
  have hstable : (prefixWord ++ tailWord_8190842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190842).length < 2 ^ (prefixWord ++ tailWord_8190842).sum := by decide
  have hdescent : baseEnd_8190842 < baseStart_8190842 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190859 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 3]
def baseStart_8190859 : Nat := 118140960795 + 8190859 * 2 ^ 59
def prefixEnd_8190859 : Nat := 4983230072969 + 3 ^ 40 * 8190859 * 2
def baseEnd_8190859 : Nat := 4205847640205273960193431

theorem tailTrace_8190859 : CollatzResearch.WordTrace tailWord_8190859 prefixEnd_8190859 4205847640205273960193431 := by
  unfold tailWord_8190859
  simp only [CollatzResearch.WordTrace]
  refine ⟨298745170632924205191199631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199163447088616136794133087 298745170632924205191199631)
  ·
    refine ⟨448117755949386307786799447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298745170632924205191199631 448117755949386307786799447)
    ·
      refine ⟨672176633924079461680199171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448117755949386307786799447 672176633924079461680199171)
      ·
        refine ⟨1008264950886119192520298757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672176633924079461680199171 1008264950886119192520298757)
        ·
          refine ⟨189049678291147348597556017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1008264950886119192520298757 189049678291147348597556017)
          ·
            refine ⟨141787258718360511448167013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189049678291147348597556017 141787258718360511448167013)
            ·
              refine ⟨26585111009692595896531315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141787258718360511448167013 26585111009692595896531315)
              ·
                refine ⟨39877666514538893844796973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26585111009692595896531315 39877666514538893844796973)
                ·
                  refine ⟨14954124942952085191798865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39877666514538893844796973 14954124942952085191798865)
                  ·
                    refine ⟨11215593707214063893849149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14954124942952085191798865 11215593707214063893849149)
                    ·
                      refine ⟨4205847640205273960193431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11215593707214063893849149 4205847640205273960193431)
                      ·
                        rfl

theorem cell23_8190859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 3].length) (baseStart_8190859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190859 prefixEnd_8190859 := by exact prefixLift 8190859
  have htrace : WordTrace (prefixWord ++ tailWord_8190859) baseStart_8190859 baseEnd_8190859 := by
    simpa [prefixWord, tailWord_8190859, baseEnd_8190859] using wordTrace_append hprefix tailTrace_8190859
  have hstable : (prefixWord ++ tailWord_8190859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190859).length < 2 ^ (prefixWord ++ tailWord_8190859).sum := by decide
  have hdescent : baseEnd_8190859 < baseStart_8190859 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190869 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 1, 2, 4]
def baseStart_8190869 : Nat := 118140960795 + 8190869 * 2 ^ 59
def prefixEnd_8190869 : Nat := 4983230072969 + 3 ^ 40 * 8190869 * 2
def baseEnd_8190869 : Nat := 4205852775011818921068385

theorem tailTrace_8190869 : CollatzResearch.WordTrace tailWord_8190869 prefixEnd_8190869 4205852775011818921068385 := by
  unfold tailWord_8190869
  simp only [CollatzResearch.WordTrace]
  refine ⟨298745535362887976899063661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199163690241925317932709107 298745535362887976899063661)
  ·
    refine ⟨112029575761082991337148873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298745535362887976899063661 112029575761082991337148873)
    ·
      refine ⟨84022181820812243502861655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112029575761082991337148873 84022181820812243502861655)
      ·
        refine ⟨126033272731218365254292483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84022181820812243502861655 126033272731218365254292483)
        ·
          refine ⟨189049909096827547881438725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126033272731218365254292483 189049909096827547881438725)
          ·
            refine ⟨35446857955655165227769761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189049909096827547881438725 35446857955655165227769761)
            ·
              refine ⟨26585143466741373920827321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35446857955655165227769761 26585143466741373920827321)
              ·
                refine ⟨19938857600056030440620491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26585143466741373920827321 19938857600056030440620491)
                ·
                  refine ⟨29908286400084045660930737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19938857600056030440620491 29908286400084045660930737)
                  ·
                    refine ⟨22431214800063034245698053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29908286400084045660930737 22431214800063034245698053)
                    ·
                      refine ⟨4205852775011818921068385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22431214800063034245698053 4205852775011818921068385)
                      ·
                        rfl

theorem cell23_8190869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_8190869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190869 prefixEnd_8190869 := by exact prefixLift 8190869
  have htrace : WordTrace (prefixWord ++ tailWord_8190869) baseStart_8190869 baseEnd_8190869 := by
    simpa [prefixWord, tailWord_8190869, baseEnd_8190869] using wordTrace_append hprefix tailTrace_8190869
  have hstable : (prefixWord ++ tailWord_8190869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190869).length < 2 ^ (prefixWord ++ tailWord_8190869).sum := by decide
  have hdescent : baseEnd_8190869 < baseStart_8190869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190870 : List Nat := [5, 3, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_8190870 : Nat := 118140960795 + 8190870 * 2 ^ 59
def prefixEnd_8190870 : Nat := 4983230072969 + 3 ^ 40 * 8190870 * 2
def baseEnd_8190870 : Nat := 1401951096164157805718627

theorem tailTrace_8190870 : CollatzResearch.WordTrace tailWord_8190870 prefixEnd_8190870 1401951096164157805718627 := by
  unfold tailWord_8190870
  simp only [CollatzResearch.WordTrace]
  refine ⟨18671598239742772129365629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199163714557256236046566709 18671598239742772129365629)
  ·
    refine ⟨7001849339903539548512111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18671598239742772129365629 7001849339903539548512111)
    ·
      refine ⟨10502774009855309322768167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7001849339903539548512111 10502774009855309322768167)
      ·
        refine ⟨15754161014782963984152251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10502774009855309322768167 15754161014782963984152251)
        ·
          refine ⟨23631241522174445976228377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15754161014782963984152251 23631241522174445976228377)
          ·
            refine ⟨17723431141630834482171283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23631241522174445976228377 17723431141630834482171283)
            ·
              refine ⟨26585146712446251723256925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17723431141630834482171283 26585146712446251723256925)
              ·
                refine ⟨9969430017167344396221347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26585146712446251723256925 9969430017167344396221347)
                ·
                  refine ⟨14954145025751016594332021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9969430017167344396221347 14954145025751016594332021)
                  ·
                    refine ⟨1401951096164157805718627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14954145025751016594332021 1401951096164157805718627)
                    ·
                      rfl

theorem cell23_8190870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_8190870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190870 prefixEnd_8190870 := by exact prefixLift 8190870
  have htrace : WordTrace (prefixWord ++ tailWord_8190870) baseStart_8190870 baseEnd_8190870 := by
    simpa [prefixWord, tailWord_8190870, baseEnd_8190870] using wordTrace_append hprefix tailTrace_8190870
  have hstable : (prefixWord ++ tailWord_8190870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190870).length < 2 ^ (prefixWord ++ tailWord_8190870).sum := by decide
  have hdescent : baseEnd_8190870 < baseStart_8190870 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190893 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 5]
def baseStart_8190893 : Nat := 118140960795 + 8190893 * 2 ^ 59
def prefixEnd_8190893 : Nat := 4983230072969 + 3 ^ 40 * 8190893 * 2
def baseEnd_8190893 : Nat := 4205865098547526827168275

theorem tailTrace_8190893 : CollatzResearch.WordTrace tailWord_8190893 prefixEnd_8190893 4205865098547526827168275 := by
  unfold tailWord_8190893
  simp only [CollatzResearch.WordTrace]
  refine ⟨298746410714801028997937333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199164273809867352665291555 298746410714801028997937333)
  ·
    refine ⟨28007476004512596468556625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298746410714801028997937333 28007476004512596468556625)
    ·
      refine ⟨21005607003384447351417469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28007476004512596468556625 21005607003384447351417469)
      ·
        refine ⟨7877102626269167756781551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21005607003384447351417469 7877102626269167756781551)
        ·
          refine ⟨11815653939403751635172327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7877102626269167756781551 11815653939403751635172327)
          ·
            refine ⟨17723480909105627452758491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11815653939403751635172327 17723480909105627452758491)
            ·
              refine ⟨26585221363658441179137737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17723480909105627452758491 26585221363658441179137737)
              ·
                refine ⟨19938916022743830884353303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26585221363658441179137737 19938916022743830884353303)
                ·
                  refine ⟨29908374034115746326529955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19938916022743830884353303 29908374034115746326529955)
                  ·
                    refine ⟨44862561051173619489794933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29908374034115746326529955 44862561051173619489794933)
                    ·
                      refine ⟨4205865098547526827168275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44862561051173619489794933 4205865098547526827168275)
                      ·
                        rfl

theorem cell23_8190893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_8190893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190893 prefixEnd_8190893 := by exact prefixLift 8190893
  have htrace : WordTrace (prefixWord ++ tailWord_8190893) baseStart_8190893 baseEnd_8190893 := by
    simpa [prefixWord, tailWord_8190893, baseEnd_8190893] using wordTrace_append hprefix tailTrace_8190893
  have hstable : (prefixWord ++ tailWord_8190893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190893).length < 2 ^ (prefixWord ++ tailWord_8190893).sum := by decide
  have hdescent : baseEnd_8190893 < baseStart_8190893 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190899 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 2, 7, 2]
def baseStart_8190899 : Nat := 118140960795 + 8190899 * 2 ^ 59
def prefixEnd_8190899 : Nat := 4983230072969 + 3 ^ 40 * 8190899 * 2
def baseEnd_8190899 : Nat := 4205868179431453803693247

theorem tailTrace_8190899 : CollatzResearch.WordTrace tailWord_8190899 prefixEnd_8190899 4205868179431453803693247 := by
  unfold tailWord_8190899
  simp only [CollatzResearch.WordTrace]
  refine ⟨298746629552779292022655751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199164419701852861348437167 298746629552779292022655751)
  ·
    refine ⟨448119944329168938033983627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298746629552779292022655751 448119944329168938033983627)
    ·
      refine ⟨672179916493753407050975441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448119944329168938033983627 672179916493753407050975441)
      ·
        refine ⟨504134937370315055288231581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672179916493753407050975441 504134937370315055288231581)
        ·
          refine ⟨189050601513868145733086843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504134937370315055288231581 189050601513868145733086843)
          ·
            refine ⟨283575902270802218599630265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189050601513868145733086843 283575902270802218599630265)
            ·
              refine ⟨212681926703101663949722699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283575902270802218599630265 212681926703101663949722699)
              ·
                refine ⟨319022890054652495924584049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212681926703101663949722699 319022890054652495924584049)
                ·
                  refine ⟨239267167540989371943438037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319022890054652495924584049 239267167540989371943438037)
                  ·
                    refine ⟨5607824239241938404924329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 239267167540989371943438037 5607824239241938404924329)
                    ·
                      refine ⟨4205868179431453803693247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5607824239241938404924329 4205868179431453803693247)
                      ·
                        rfl

theorem cell23_8190899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 7, 2].length) (baseStart_8190899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190899 prefixEnd_8190899 := by exact prefixLift 8190899
  have htrace : WordTrace (prefixWord ++ tailWord_8190899) baseStart_8190899 baseEnd_8190899 := by
    simpa [prefixWord, tailWord_8190899, baseEnd_8190899] using wordTrace_append hprefix tailTrace_8190899
  have hstable : (prefixWord ++ tailWord_8190899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190899).length < 2 ^ (prefixWord ++ tailWord_8190899).sum := by decide
  have hdescent : baseEnd_8190899 < baseStart_8190899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190918 : List Nat := [6, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3]
def baseStart_8190918 : Nat := 118140960795 + 8190918 * 2 ^ 59
def prefixEnd_8190918 : Nat := 4983230072969 + 3 ^ 40 * 8190918 * 2
def baseEnd_8190918 : Nat := 4205877935563889229355661

theorem tailTrace_8190918 : CollatzResearch.WordTrace tailWord_8190918 prefixEnd_8190918 4205877935563889229355661 := by
  unfold tailWord_8190918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9335853829365951820862419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199164881693140305511731605 9335853829365951820862419)
  ·
    refine ⟨14003780744048927731293629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9335853829365951820862419 14003780744048927731293629)
    ·
      refine ⟨5251417779018347899235111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14003780744048927731293629 5251417779018347899235111)
      ·
        refine ⟨7877126668527521848852667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5251417779018347899235111 7877126668527521848852667)
        ·
          refine ⟨11815690002791282773279001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7877126668527521848852667 11815690002791282773279001)
          ·
            refine ⟨8861767502093462079959251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11815690002791282773279001 8861767502093462079959251)
            ·
              refine ⟨13292651253140193119938877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8861767502093462079959251 13292651253140193119938877)
              ·
                refine ⟨4984744219927572419977079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13292651253140193119938877 4984744219927572419977079)
                ·
                  refine ⟨7477116329891358629965619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4984744219927572419977079 7477116329891358629965619)
                  ·
                    refine ⟨11215674494837037944948429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7477116329891358629965619 11215674494837037944948429)
                    ·
                      refine ⟨4205877935563889229355661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11215674494837037944948429 4205877935563889229355661)
                      ·
                        rfl

theorem cell23_8190918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_8190918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190918 prefixEnd_8190918 := by exact prefixLift 8190918
  have htrace : WordTrace (prefixWord ++ tailWord_8190918) baseStart_8190918 baseEnd_8190918 := by
    simpa [prefixWord, tailWord_8190918, baseEnd_8190918] using wordTrace_append hprefix tailTrace_8190918
  have hstable : (prefixWord ++ tailWord_8190918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190918).length < 2 ^ (prefixWord ++ tailWord_8190918).sum := by decide
  have hdescent : baseEnd_8190918 < baseStart_8190918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190966 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_8190966 : Nat := 118140960795 + 8190966 * 2 ^ 59
def prefixEnd_8190966 : Nat := 4983230072969 + 3 ^ 40 * 8190966 * 2
def baseEnd_8190966 : Nat := 4205902582635305041555439

theorem tailTrace_8190966 : CollatzResearch.WordTrace tailWord_8190966 prefixEnd_8190966 4205902582635305041555439 := by
  unfold tailWord_8190966
  simp only [CollatzResearch.WordTrace]
  refine ⟨18671817077721035154084047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199166048829024374976896501 18671817077721035154084047)
  ·
    refine ⟨28007725616581552731126071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18671817077721035154084047 28007725616581552731126071)
    ·
      refine ⟨42011588424872329096689107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28007725616581552731126071 42011588424872329096689107)
      ·
        refine ⟨63017382637308493645033661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42011588424872329096689107 63017382637308493645033661)
        ·
          refine ⟨23631518488990685116887623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63017382637308493645033661 23631518488990685116887623)
          ·
            refine ⟨35447277733486027675331435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23631518488990685116887623 35447277733486027675331435)
            ·
              refine ⟨53170916600229041512997153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35447277733486027675331435 53170916600229041512997153)
              ·
                refine ⟨39878187450171781134747865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53170916600229041512997153 39878187450171781134747865)
                ·
                  refine ⟨29908640587628835851060899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39878187450171781134747865 29908640587628835851060899)
                  ·
                    refine ⟨44862960881443253776591349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29908640587628835851060899 44862960881443253776591349)
                    ·
                      refine ⟨4205902582635305041555439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44862960881443253776591349 4205902582635305041555439)
                      ·
                        rfl

theorem cell23_8190966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_8190966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190966 prefixEnd_8190966 := by exact prefixLift 8190966
  have htrace : WordTrace (prefixWord ++ tailWord_8190966) baseStart_8190966 baseEnd_8190966 := by
    simpa [prefixWord, tailWord_8190966, baseEnd_8190966] using wordTrace_append hprefix tailTrace_8190966
  have hstable : (prefixWord ++ tailWord_8190966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190966).length < 2 ^ (prefixWord ++ tailWord_8190966).sum := by decide
  have hdescent : baseEnd_8190966 < baseStart_8190966 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8190979 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 3]
def baseStart_8190979 : Nat := 118140960795 + 8190979 * 2 ^ 59
def prefixEnd_8190979 : Nat := 4983230072969 + 3 ^ 40 * 8190979 * 2
def baseEnd_8190979 : Nat := 4205909257883813490692879

theorem tailTrace_8190979 : CollatzResearch.WordTrace tailWord_8190979 prefixEnd_8190979 4205909257883813490692879 := by
  unfold tailWord_8190979
  simp only [CollatzResearch.WordTrace]
  refine ⟨298749547392489465685567991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199166364928326310457045327 298749547392489465685567991)
  ·
    refine ⟨448124321088734198528351987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298749547392489465685567991 448124321088734198528351987)
    ·
      refine ⟨672186481633101297792527981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448124321088734198528351987 672186481633101297792527981)
      ·
        refine ⟨252069930612412986672197993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 672186481633101297792527981 252069930612412986672197993)
        ·
          refine ⟨189052447959309740004148495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252069930612412986672197993 189052447959309740004148495)
          ·
            refine ⟨283578671938964610006222743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189052447959309740004148495 283578671938964610006222743)
            ·
              refine ⟨425368007908446915009334115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283578671938964610006222743 425368007908446915009334115)
              ·
                refine ⟨638052011862670372514001173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425368007908446915009334115 638052011862670372514001173)
                ·
                  refine ⟨29908688056062673711593805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 638052011862670372514001173 29908688056062673711593805)
                  ·
                    refine ⟨11215758021023502641847677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29908688056062673711593805 11215758021023502641847677)
                    ·
                      refine ⟨4205909257883813490692879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11215758021023502641847677 4205909257883813490692879)
                      ·
                        rfl

theorem cell23_8190979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 3].length) (baseStart_8190979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8190979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8190979 prefixEnd_8190979 := by exact prefixLift 8190979
  have htrace : WordTrace (prefixWord ++ tailWord_8190979) baseStart_8190979 baseEnd_8190979 := by
    simpa [prefixWord, tailWord_8190979, baseEnd_8190979] using wordTrace_append hprefix tailTrace_8190979
  have hstable : (prefixWord ++ tailWord_8190979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8190979).length < 2 ^ (prefixWord ++ tailWord_8190979).sum := by decide
  have hdescent : baseEnd_8190979 < baseStart_8190979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8190979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191019 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 4]
def baseStart_8191019 : Nat := 118140960795 + 8191019 * 2 ^ 59
def prefixEnd_8191019 : Nat := 4983230072969 + 3 ^ 40 * 8191019 * 2
def baseEnd_8191019 : Nat := 4205929797109993334192695

theorem tailTrace_8191019 : CollatzResearch.WordTrace tailWord_8191019 prefixEnd_8191019 4205929797109993334192695 := by
  unfold tailWord_8191019
  simp only [CollatzResearch.WordTrace]
  refine ⟨298751006312344552517024111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199167337541563035011349407 298751006312344552517024111)
  ·
    refine ⟨448126509468516828775536167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298751006312344552517024111 448126509468516828775536167)
    ·
      refine ⟨672189764202775243163304251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448126509468516828775536167 672189764202775243163304251)
      ·
        refine ⟨1008284646304162864744956377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672189764202775243163304251 1008284646304162864744956377)
        ·
          refine ⟨756213484728122148558717283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1008284646304162864744956377 756213484728122148558717283)
          ·
            refine ⟨1134320227092183222838075925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756213484728122148558717283 1134320227092183222838075925)
            ·
              refine ⟨53171260644946088570534809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1134320227092183222838075925 53171260644946088570534809)
              ·
                refine ⟨39878445483709566427901107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53171260644946088570534809 39878445483709566427901107)
                ·
                  refine ⟨59817668225564349641851661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39878445483709566427901107 59817668225564349641851661)
                  ·
                    refine ⟨22431625584586631115694373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59817668225564349641851661 22431625584586631115694373)
                    ·
                      refine ⟨4205929797109993334192695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22431625584586631115694373 4205929797109993334192695)
                      ·
                        rfl

theorem cell23_8191019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 4].length) (baseStart_8191019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191019 prefixEnd_8191019 := by exact prefixLift 8191019
  have htrace : WordTrace (prefixWord ++ tailWord_8191019) baseStart_8191019 baseEnd_8191019 := by
    simpa [prefixWord, tailWord_8191019, baseEnd_8191019] using wordTrace_append hprefix tailTrace_8191019
  have hstable : (prefixWord ++ tailWord_8191019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191019).length < 2 ^ (prefixWord ++ tailWord_8191019).sum := by decide
  have hdescent : baseEnd_8191019 < baseStart_8191019 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191033 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 2, 5]
def baseStart_8191033 : Nat := 118140960795 + 8191033 * 2 ^ 59
def prefixEnd_8191033 : Nat := 4983230072969 + 3 ^ 40 * 8191033 * 2
def baseEnd_8191033 : Nat := 1401978995279718759805877

theorem tailTrace_8191033 : CollatzResearch.WordTrace tailWord_8191033 prefixEnd_8191033 1401978995279718759805877 := by
  unfold tailWord_8191033
  simp only [CollatzResearch.WordTrace]
  refine ⟨298751516934293832908033753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199167677956195888605355835 298751516934293832908033753)
  ·
    refine ⟨224063637700720374681025315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298751516934293832908033753 224063637700720374681025315)
    ·
      refine ⟨336095456551080562021537973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224063637700720374681025315 336095456551080562021537973)
      ·
        refine ⟨31508949051663802689519185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 336095456551080562021537973 31508949051663802689519185)
        ·
          refine ⟨23631711788747852017139389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31508949051663802689519185 23631711788747852017139389)
          ·
            refine ⟨8861891920780444506427271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23631711788747852017139389 8861891920780444506427271)
            ·
              refine ⟨13292837881170666759640907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8861891920780444506427271 13292837881170666759640907)
              ·
                refine ⟨19939256821756000139461361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13292837881170666759640907 19939256821756000139461361)
                ·
                  refine ⟨14954442616317000104596021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19939256821756000139461361 14954442616317000104596021)
                  ·
                    refine ⟨1401978995279718759805877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14954442616317000104596021 1401978995279718759805877)
                    ·
                      rfl

theorem cell23_8191033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 5].length) (baseStart_8191033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191033 prefixEnd_8191033 := by exact prefixLift 8191033
  have htrace : WordTrace (prefixWord ++ tailWord_8191033) baseStart_8191033 baseEnd_8191033 := by
    simpa [prefixWord, tailWord_8191033, baseEnd_8191033] using wordTrace_append hprefix tailTrace_8191033
  have hstable : (prefixWord ++ tailWord_8191033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191033).length < 2 ^ (prefixWord ++ tailWord_8191033).sum := by decide
  have hdescent : baseEnd_8191033 < baseStart_8191033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191036 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_8191036 : Nat := 118140960795 + 8191036 * 2 ^ 59
def prefixEnd_8191036 : Nat := 4983230072969 + 3 ^ 40 * 8191036 * 2
def baseEnd_8191036 : Nat := 4205938526281119767680117

theorem tailTrace_8191036 : CollatzResearch.WordTrace tailWord_8191036 prefixEnd_8191036 4205938526281119767680117 := by
  unfold tailWord_8191036
  simp only [CollatzResearch.WordTrace]
  refine ⟨149375813176641482210196481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199167750902188642946928641 149375813176641482210196481)
  ·
    refine ⟨112031859882481111657647361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149375813176641482210196481 112031859882481111657647361)
    ·
      refine ⟨84023894911860833743235521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112031859882481111657647361 84023894911860833743235521)
      ·
        refine ⟨63017921183895625307426641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84023894911860833743235521 63017921183895625307426641)
        ·
          refine ⟨47263440887921718980569981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63017921183895625307426641 47263440887921718980569981)
          ·
            refine ⟨17723790332970644617713743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47263440887921718980569981 17723790332970644617713743)
            ·
              refine ⟨26585685499455966926570615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17723790332970644617713743 26585685499455966926570615)
              ·
                refine ⟨39878528249183950389855923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26585685499455966926570615 39878528249183950389855923)
                ·
                  refine ⟨59817792373775925584783885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39878528249183950389855923 59817792373775925584783885)
                  ·
                    refine ⟨22431672140165972094293957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59817792373775925584783885 22431672140165972094293957)
                    ·
                      refine ⟨4205938526281119767680117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22431672140165972094293957 4205938526281119767680117)
                      ·
                        rfl

theorem cell23_8191036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_8191036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191036 prefixEnd_8191036 := by exact prefixLift 8191036
  have htrace : WordTrace (prefixWord ++ tailWord_8191036) baseStart_8191036 baseEnd_8191036 := by
    simpa [prefixWord, tailWord_8191036, baseEnd_8191036] using wordTrace_append hprefix tailTrace_8191036
  have hstable : (prefixWord ++ tailWord_8191036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191036).length < 2 ^ (prefixWord ++ tailWord_8191036).sum := by decide
  have hdescent : baseEnd_8191036 < baseStart_8191036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191056 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 3]
def baseStart_8191056 : Nat := 118140960795 + 8191056 * 2 ^ 59
def prefixEnd_8191056 : Nat := 4983230072969 + 3 ^ 40 * 8191056 * 2
def baseEnd_8191056 : Nat := 4205948795894209689430025

theorem tailTrace_8191056 : CollatzResearch.WordTrace tailWord_8191056 prefixEnd_8191056 4205948795894209689430025 := by
  unfold tailWord_8191056
  simp only [CollatzResearch.WordTrace]
  refine ⟨149376177906605253918060511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199168237208807005224080681 149376177906605253918060511)
  ·
    refine ⟨224064266859907880877090767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149376177906605253918060511 224064266859907880877090767)
    ·
      refine ⟨336096400289861821315636151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224064266859907880877090767 336096400289861821315636151)
      ·
        refine ⟨504144600434792731973454227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336096400289861821315636151 504144600434792731973454227)
        ·
          refine ⟨756216900652189097960181341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504144600434792731973454227 756216900652189097960181341)
          ·
            refine ⟨283581337744570911735068003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 756216900652189097960181341 283581337744570911735068003)
            ·
              refine ⟨425372006616856367602602005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283581337744570911735068003 425372006616856367602602005)
              ·
                refine ⟨19939312810165142231371969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 425372006616856367602602005 19939312810165142231371969)
                ·
                  refine ⟨14954484607623856673528977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19939312810165142231371969 14954484607623856673528977)
                  ·
                    refine ⟨11215863455717892505146733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14954484607623856673528977 11215863455717892505146733)
                    ·
                      refine ⟨4205948795894209689430025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11215863455717892505146733 4205948795894209689430025)
                      ·
                        rfl

theorem cell23_8191056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 3].length) (baseStart_8191056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191056 prefixEnd_8191056 := by exact prefixLift 8191056
  have htrace : WordTrace (prefixWord ++ tailWord_8191056) baseStart_8191056 baseEnd_8191056 := by
    simpa [prefixWord, tailWord_8191056, baseEnd_8191056] using wordTrace_append hprefix tailTrace_8191056
  have hstable : (prefixWord ++ tailWord_8191056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191056).length < 2 ^ (prefixWord ++ tailWord_8191056).sum := by decide
  have hdescent : baseEnd_8191056 < baseStart_8191056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191070 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_8191070 : Nat := 118140960795 + 8191070 * 2 ^ 59
def prefixEnd_8191070 : Nat := 4983230072969 + 3 ^ 40 * 8191070 * 2
def baseEnd_8191070 : Nat := 4205955984623372634654961

theorem tailTrace_8191070 : CollatzResearch.WordTrace tailWord_8191070 prefixEnd_8191070 4205955984623372634654961 := by
  unfold tailWord_8191070
  simp only [CollatzResearch.WordTrace]
  refine ⟨37344108304394973528391333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199168577623439858818087109 37344108304394973528391333)
  ·
    refine ⟨7002020307074057536573375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37344108304394973528391333 7002020307074057536573375)
    ·
      refine ⟨10503030460611086304860063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7002020307074057536573375 10503030460611086304860063)
      ·
        refine ⟨15754545690916629457290095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10503030460611086304860063 15754545690916629457290095)
        ·
          refine ⟨23631818536374944185935143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15754545690916629457290095 23631818536374944185935143)
          ·
            refine ⟨35447727804562416278902715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23631818536374944185935143 35447727804562416278902715)
            ·
              refine ⟨53171591706843624418354073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35447727804562416278902715 53171591706843624418354073)
              ·
                refine ⟨39878693780132718313765555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53171591706843624418354073 39878693780132718313765555)
                ·
                  refine ⟨59818040670199077470648333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39878693780132718313765555 59818040670199077470648333)
                  ·
                    refine ⟨22431765251324654051493125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59818040670199077470648333 22431765251324654051493125)
                    ·
                      refine ⟨4205955984623372634654961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22431765251324654051493125 4205955984623372634654961)
                      ·
                        rfl

theorem cell23_8191070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_8191070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191070 prefixEnd_8191070 := by exact prefixLift 8191070
  have htrace : WordTrace (prefixWord ++ tailWord_8191070) baseStart_8191070 baseEnd_8191070 := by
    simpa [prefixWord, tailWord_8191070, baseEnd_8191070] using wordTrace_append hprefix tailTrace_8191070
  have hstable : (prefixWord ++ tailWord_8191070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191070).length < 2 ^ (prefixWord ++ tailWord_8191070).sum := by decide
  have hdescent : baseEnd_8191070 < baseStart_8191070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191097 : List Nat := [1, 2, 1, 3, 5, 2, 1, 3, 1, 4]
def baseStart_8191097 : Nat := 118140960795 + 8191097 * 2 ^ 59
def prefixEnd_8191097 : Nat := 4983230072969 + 3 ^ 40 * 8191097 * 2
def baseEnd_8191097 : Nat := 1401989949533681343005779

theorem tailTrace_8191097 : CollatzResearch.WordTrace tailWord_8191097 prefixEnd_8191097 1401989949533681343005779 := by
  unfold tailWord_8191097
  simp only [CollatzResearch.WordTrace]
  refine ⟨298753851206061971838363545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199169234137374647892242363 298753851206061971838363545)
  ·
    refine ⟨224065388404546478878772659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298753851206061971838363545 224065388404546478878772659)
    ·
      refine ⟨336098082606819718318158989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224065388404546478878772659 336098082606819718318158989)
      ·
        refine ⟨126036780977557394369309621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336098082606819718318158989 126036780977557394369309621)
        ·
          refine ⟨11815948216646005722122777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126036780977557394369309621 11815948216646005722122777)
          ·
            refine ⟨8861961162484504291592083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11815948216646005722122777 8861961162484504291592083)
            ·
              refine ⟨13292941743726756437388125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8861961162484504291592083 13292941743726756437388125)
              ·
                refine ⟨4984853153897533664020547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13292941743726756437388125 4984853153897533664020547)
                ·
                  refine ⟨7477279730846300496030821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4984853153897533664020547 7477279730846300496030821)
                  ·
                    refine ⟨1401989949533681343005779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7477279730846300496030821 1401989949533681343005779)
                    ·
                      rfl

theorem cell23_8191097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 1, 4].length) (baseStart_8191097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191097 prefixEnd_8191097 := by exact prefixLift 8191097
  have htrace : WordTrace (prefixWord ++ tailWord_8191097) baseStart_8191097 baseEnd_8191097 := by
    simpa [prefixWord, tailWord_8191097, baseEnd_8191097] using wordTrace_append hprefix tailTrace_8191097
  have hstable : (prefixWord ++ tailWord_8191097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191097).length < 2 ^ (prefixWord ++ tailWord_8191097).sum := by decide
  have hdescent : baseEnd_8191097 < baseStart_8191097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191113 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 4, 3, 2]
def baseStart_8191113 : Nat := 118140960795 + 8191113 * 2 ^ 59
def prefixEnd_8191113 : Nat := 4983230072969 + 3 ^ 40 * 8191113 * 2
def baseEnd_8191113 : Nat := 4205978064291515966417263

theorem tailTrace_8191113 : CollatzResearch.WordTrace tailWord_8191113 prefixEnd_8191113 4205978064291515966417263 := by
  unfold tailWord_8191113
  simp only [CollatzResearch.WordTrace]
  refine ⟨298754434774004006570945993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199169623182669337713963995 298754434774004006570945993)
  ·
    refine ⟨224065826080503004928209495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298754434774004006570945993 224065826080503004928209495)
    ·
      refine ⟨336098739120754507392314243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224065826080503004928209495 336098739120754507392314243)
      ·
        refine ⟨504148108681131761088471365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336098739120754507392314243 504148108681131761088471365)
        ·
          refine ⟨94527770377712205204088381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 504148108681131761088471365 94527770377712205204088381)
          ·
            refine ⟨35447913891642076951533143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94527770377712205204088381 35447913891642076951533143)
            ·
              refine ⟨53171870837463115427299715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35447913891642076951533143 53171870837463115427299715)
              ·
                refine ⟨79757806256194673140949573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53171870837463115427299715 79757806256194673140949573)
                ·
                  refine ⟨14954588673036501213928045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79757806256194673140949573 14954588673036501213928045)
                  ·
                    refine ⟨5607970752388687955223017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14954588673036501213928045 5607970752388687955223017)
                    ·
                      refine ⟨4205978064291515966417263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5607970752388687955223017 4205978064291515966417263)
                      ·
                        rfl

theorem cell23_8191113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 3, 2].length) (baseStart_8191113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191113 prefixEnd_8191113 := by exact prefixLift 8191113
  have htrace : WordTrace (prefixWord ++ tailWord_8191113) baseStart_8191113 baseEnd_8191113 := by
    simpa [prefixWord, tailWord_8191113, baseEnd_8191113] using wordTrace_append hprefix tailTrace_8191113
  have hstable : (prefixWord ++ tailWord_8191113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191113).length < 2 ^ (prefixWord ++ tailWord_8191113).sum := by decide
  have hdescent : baseEnd_8191113 < baseStart_8191113 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191136 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 1, 6]
def baseStart_8191136 : Nat := 118140960795 + 8191136 * 2 ^ 59
def prefixEnd_8191136 : Nat := 4983230072969 + 3 ^ 40 * 8191136 * 2
def baseEnd_8191136 : Nat := 1401996624782189792143219

theorem tailTrace_8191136 : CollatzResearch.WordTrace tailWord_8191136 prefixEnd_8191136 1401996624782189792143219 := by
  unfold tailWord_8191136
  simp only [CollatzResearch.WordTrace]
  refine ⟨149377636826460340749516631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199170182435280454332688841 149377636826460340749516631)
  ·
    refine ⟨224066455239690511124274947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149377636826460340749516631 224066455239690511124274947)
    ·
      refine ⟨336099682859535766686412421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224066455239690511124274947 336099682859535766686412421)
      ·
        refine ⟨63018690536162956253702329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336099682859535766686412421 63018690536162956253702329)
        ·
          refine ⟨47264017902122217190276747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63018690536162956253702329 47264017902122217190276747)
          ·
            refine ⟨70896026853183325785415121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47264017902122217190276747 70896026853183325785415121)
            ·
              refine ⟨53172020139887494339061341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70896026853183325785415121 53172020139887494339061341)
              ·
                refine ⟨19939507552457810377148003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53172020139887494339061341 19939507552457810377148003)
                ·
                  refine ⟨29909261328686715565722005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19939507552457810377148003 29909261328686715565722005)
                  ·
                    refine ⟨1401996624782189792143219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29909261328686715565722005 1401996624782189792143219)
                    ·
                      rfl

theorem cell23_8191136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 6].length) (baseStart_8191136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191136 prefixEnd_8191136 := by exact prefixLift 8191136
  have htrace : WordTrace (prefixWord ++ tailWord_8191136) baseStart_8191136 baseEnd_8191136 := by
    simpa [prefixWord, tailWord_8191136, baseEnd_8191136] using wordTrace_append hprefix tailTrace_8191136
  have hstable : (prefixWord ++ tailWord_8191136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191136).length < 2 ^ (prefixWord ++ tailWord_8191136).sum := by decide
  have hdescent : baseEnd_8191136 < baseStart_8191136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191140 : List Nat := [2, 3, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_8191140 : Nat := 118140960795 + 8191140 * 2 ^ 59
def prefixEnd_8191140 : Nat := 4983230072969 + 3 ^ 40 * 8191140 * 2
def baseEnd_8191140 : Nat := 1401997309423062453593213

theorem tailTrace_8191140 : CollatzResearch.WordTrace tailWord_8191140 prefixEnd_8191140 1401997309423062453593213 := by
  unfold tailWord_8191140
  simp only [CollatzResearch.WordTrace]
  refine ⟨149377709772453095091089437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199170279696604126788119249 149377709772453095091089437)
  ·
    refine ⟨56016641164669910659158539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149377709772453095091089437 56016641164669910659158539)
    ·
      refine ⟨84024961747004865988737809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56016641164669910659158539 84024961747004865988737809)
      ·
        refine ⟨63018721310253649491553357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84024961747004865988737809 63018721310253649491553357)
        ·
          refine ⟨23632020491345118559332509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63018721310253649491553357 23632020491345118559332509)
          ·
            refine ⟨8862007684254419459749691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23632020491345118559332509 8862007684254419459749691)
            ·
              refine ⟨13293011526381629189624537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8862007684254419459749691 13293011526381629189624537)
              ·
                refine ⟨9969758644786221892218403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13293011526381629189624537 9969758644786221892218403)
                ·
                  refine ⟨14954637967179332838327605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9969758644786221892218403 14954637967179332838327605)
                  ·
                    refine ⟨1401997309423062453593213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14954637967179332838327605 1401997309423062453593213)
                    ·
                      rfl

theorem cell23_8191140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_8191140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191140 prefixEnd_8191140 := by exact prefixLift 8191140
  have htrace : WordTrace (prefixWord ++ tailWord_8191140) baseStart_8191140 baseEnd_8191140 := by
    simpa [prefixWord, tailWord_8191140, baseEnd_8191140] using wordTrace_append hprefix tailTrace_8191140
  have hstable : (prefixWord ++ tailWord_8191140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191140).length < 2 ^ (prefixWord ++ tailWord_8191140).sum := by decide
  have hdescent : baseEnd_8191140 < baseStart_8191140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191153 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 1, 6]
def baseStart_8191153 : Nat := 118140960795 + 8191153 * 2 ^ 59
def prefixEnd_8191153 : Nat := 4983230072969 + 3 ^ 40 * 8191153 * 2
def baseEnd_8191153 : Nat := 1401999534505898603305693

theorem tailTrace_8191153 : CollatzResearch.WordTrace tailWord_8191153 prefixEnd_8191153 1401999534505898603305693 := by
  unfold tailWord_8191153
  simp only [CollatzResearch.WordTrace]
  refine ⟨298755893693859093402402113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199170595795906062268268075 298755893693859093402402113)
  ·
    refine ⟨224066920270394320051801585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298755893693859093402402113 224066920270394320051801585)
    ·
      refine ⟨168050190202795740038851189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224066920270394320051801585 168050190202795740038851189)
      ·
        refine ⟨15754705331512100628642299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168050190202795740038851189 15754705331512100628642299)
        ·
          refine ⟨23632057997268150942963449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15754705331512100628642299 23632057997268150942963449)
          ·
            refine ⟨17724043497951113207222587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23632057997268150942963449 17724043497951113207222587)
            ·
              refine ⟨26586065246926669810833881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17724043497951113207222587 26586065246926669810833881)
              ·
                refine ⟨19939548935195002358125411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26586065246926669810833881 19939548935195002358125411)
                ·
                  refine ⟨29909323402792503537188117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19939548935195002358125411 29909323402792503537188117)
                  ·
                    refine ⟨1401999534505898603305693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29909323402792503537188117 1401999534505898603305693)
                    ·
                      rfl

theorem cell23_8191153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_8191153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191153 prefixEnd_8191153 := by exact prefixLift 8191153
  have htrace : WordTrace (prefixWord ++ tailWord_8191153) baseStart_8191153 baseEnd_8191153 := by
    simpa [prefixWord, tailWord_8191153, baseEnd_8191153] using wordTrace_append hprefix tailTrace_8191153
  have hstable : (prefixWord ++ tailWord_8191153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191153).length < 2 ^ (prefixWord ++ tailWord_8191153).sum := by decide
  have hdescent : baseEnd_8191153 < baseStart_8191153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191166 : List Nat := [4, 2, 1, 1, 3, 12]
def baseStart_8191166 : Nat := 118140960795 + 8191166 * 2 ^ 59
def prefixEnd_8191166 : Nat := 4983230072969 + 3 ^ 40 * 8191166 * 2
def baseEnd_8191166 : Nat := 17308663698626354975533

theorem tailTrace_8191166 : CollatzResearch.WordTrace tailWord_8191166 prefixEnd_8191166 17308663698626354975533 := by
  unfold tailWord_8191166
  simp only [CollatzResearch.WordTrace]
  refine ⟨37344545980351499577828169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199170911895207997748416901 37344545980351499577828169)
  ·
    refine ⟨28008409485263624683371127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37344545980351499577828169 28008409485263624683371127)
    ·
      refine ⟨42012614227895437025056691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28008409485263624683371127 42012614227895437025056691)
      ·
        refine ⟨63018921341843155537585037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42012614227895437025056691 63018921341843155537585037)
        ·
          refine ⟨23632095503191183326594389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63018921341843155537585037 23632095503191183326594389)
          ·
            refine ⟨17308663698626354975533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23632095503191183326594389 17308663698626354975533)
            ·
              rfl

theorem cell23_8191166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 12].length) (baseStart_8191166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191166 prefixEnd_8191166 := by exact prefixLift 8191166
  have htrace : WordTrace (prefixWord ++ tailWord_8191166) baseStart_8191166 baseEnd_8191166 := by
    simpa [prefixWord, tailWord_8191166, baseEnd_8191166] using wordTrace_append hprefix tailTrace_8191166
  have hstable : (prefixWord ++ tailWord_8191166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191166).length < 2 ^ (prefixWord ++ tailWord_8191166).sum := by decide
  have hdescent : baseEnd_8191166 < baseStart_8191166 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191193 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 6, 1, 3]
def baseStart_8191193 : Nat := 118140960795 + 8191193 * 2 ^ 59
def prefixEnd_8191193 : Nat := 4983230072969 + 3 ^ 40 * 8191193 * 2
def baseEnd_8191193 : Nat := 4206019142743875653416895

theorem tailTrace_8191193 : CollatzResearch.WordTrace tailWord_8191193 prefixEnd_8191193 4206019142743875653416895 := by
  unfold tailWord_8191193
  simp only [CollatzResearch.WordTrace]
  refine ⟨298757352613714180233858233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199171568409142786822572155 298757352613714180233858233)
  ·
    refine ⟨224068014460285635175393675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298757352613714180233858233 224068014460285635175393675)
    ·
      refine ⟨336102021690428452763090513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224068014460285635175393675 336102021690428452763090513)
      ·
        refine ⟨252076516267821339572317885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336102021690428452763090513 252076516267821339572317885)
        ·
          refine ⟨94528693600433002339619207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252076516267821339572317885 94528693600433002339619207)
          ·
            refine ⟨141793040400649503509428811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94528693600433002339619207 141793040400649503509428811)
            ·
              refine ⟨212689560600974255264143217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141793040400649503509428811 212689560600974255264143217)
              ·
                refine ⟨159517170450730691448107413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212689560600974255264143217 159517170450730691448107413)
                ·
                  refine ⟨7477367364878001161630035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159517170450730691448107413 7477367364878001161630035)
                  ·
                    refine ⟨11216051047317001742445053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7477367364878001161630035 11216051047317001742445053)
                    ·
                      refine ⟨4206019142743875653416895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11216051047317001742445053 4206019142743875653416895)
                      ·
                        rfl

theorem cell23_8191193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_8191193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191193 prefixEnd_8191193 := by exact prefixLift 8191193
  have htrace : WordTrace (prefixWord ++ tailWord_8191193) baseStart_8191193 baseEnd_8191193 := by
    simpa [prefixWord, tailWord_8191193, baseEnd_8191193] using wordTrace_append hprefix tailTrace_8191193
  have hstable : (prefixWord ++ tailWord_8191193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191193).length < 2 ^ (prefixWord ++ tailWord_8191193).sum := by decide
  have hdescent : baseEnd_8191193 < baseStart_8191193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191226 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 4, 6]
def baseStart_8191226 : Nat := 118140960795 + 8191226 * 2 ^ 59
def prefixEnd_8191226 : Nat := 4983230072969 + 3 ^ 40 * 8191226 * 2
def baseEnd_8191226 : Nat := 1402012029201824674768081

theorem tailTrace_8191226 : CollatzResearch.WordTrace tailWord_8191226 prefixEnd_8191226 1402012029201824674768081 := by
  unfold tailWord_8191226
  simp only [CollatzResearch.WordTrace]
  refine ⟨74689639055648656717452383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199172370815063084579873021 74689639055648656717452383)
  ·
    refine ⟨112034458583472985076178575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74689639055648656717452383 112034458583472985076178575)
    ·
      refine ⟨168051687875209477614267863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112034458583472985076178575 168051687875209477614267863)
      ·
        refine ⟨252077531812814216421401795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168051687875209477614267863 252077531812814216421401795)
        ·
          refine ⟨378116297719221324632102693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252077531812814216421401795 378116297719221324632102693)
          ·
            refine ⟨70896805822353998368519255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378116297719221324632102693 70896805822353998368519255)
            ·
              refine ⟨106345208733530997552778883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70896805822353998368519255 106345208733530997552778883)
              ·
                refine ⟨159517813100296496329168325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106345208733530997552778883 159517813100296496329168325)
                ·
                  refine ⟨29909589956305593061719061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159517813100296496329168325 29909589956305593061719061)
                  ·
                    refine ⟨1402012029201824674768081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29909589956305593061719061 1402012029201824674768081)
                    ·
                      rfl

theorem cell23_8191226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_8191226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191226 prefixEnd_8191226 := by exact prefixLift 8191226
  have htrace : WordTrace (prefixWord ++ tailWord_8191226) baseStart_8191226 baseEnd_8191226 := by
    simpa [prefixWord, tailWord_8191226, baseEnd_8191226] using wordTrace_append hprefix tailTrace_8191226
  have hstable : (prefixWord ++ tailWord_8191226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191226).length < 2 ^ (prefixWord ++ tailWord_8191226).sum := by decide
  have hdescent : baseEnd_8191226 < baseStart_8191226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191284 : List Nat := [2, 5, 1, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_8191284 : Nat := 118140960795 + 8191284 * 2 ^ 59
def prefixEnd_8191284 : Nat := 4983230072969 + 3 ^ 40 * 8191284 * 2
def baseEnd_8191284 : Nat := 4206065869483434797378977

theorem tailTrace_8191284 : CollatzResearch.WordTrace tailWord_8191284 prefixEnd_8191284 4206065869483434797378977 := by
  unfold tailWord_8191284
  simp only [CollatzResearch.WordTrace]
  refine ⟨149380335828192251387710453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199173781104256335183613937 149380335828192251387710453)
  ·
    refine ⟨14004406483893023567597855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149380335828192251387710453 14004406483893023567597855)
    ·
      refine ⟨21006609725839535351396783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14004406483893023567597855 21006609725839535351396783)
      ·
        refine ⟨31509914588759303027095175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21006609725839535351396783 31509914588759303027095175)
        ·
          refine ⟨47264871883138954540642763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31509914588759303027095175 47264871883138954540642763)
          ·
            refine ⟨70897307824708431810964145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47264871883138954540642763 70897307824708431810964145)
            ·
              refine ⟨53172980868531323858223109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70897307824708431810964145 53172980868531323858223109)
              ·
                refine ⟨9969933912849623223416833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53172980868531323858223109 9969933912849623223416833)
                ·
                  refine ⟨7477450434637217417562625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9969933912849623223416833 7477450434637217417562625)
                  ·
                    refine ⟨5608087825977913063171969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7477450434637217417562625 5608087825977913063171969)
                    ·
                      refine ⟨4206065869483434797378977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5608087825977913063171969 4206065869483434797378977)
                      ·
                        rfl

theorem cell23_8191284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_8191284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191284 prefixEnd_8191284 := by exact prefixLift 8191284
  have htrace : WordTrace (prefixWord ++ tailWord_8191284) baseStart_8191284 baseEnd_8191284 := by
    simpa [prefixWord, tailWord_8191284, baseEnd_8191284] using wordTrace_append hprefix tailTrace_8191284
  have hstable : (prefixWord ++ tailWord_8191284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191284).length < 2 ^ (prefixWord ++ tailWord_8191284).sum := by decide
  have hdescent : baseEnd_8191284 < baseStart_8191284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191318 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_8191318 : Nat := 118140960795 + 8191318 * 2 ^ 59
def prefixEnd_8191318 : Nat := 4983230072969 + 3 ^ 40 * 8191318 * 2
def baseEnd_8191318 : Nat := 4206083327825687664353821

theorem tailTrace_8191318 : CollatzResearch.WordTrace tailWord_8191318 prefixEnd_8191318 4206083327825687664353821 := by
  unfold tailWord_8191318
  simp only [CollatzResearch.WordTrace]
  refine ⟨18672619483641332911384913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199174607825507551054772405 18672619483641332911384913)
  ·
    refine ⟨14004464612730999683538685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18672619483641332911384913 14004464612730999683538685)
    ·
      refine ⟨5251674229774124881327007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14004464612730999683538685 5251674229774124881327007)
      ·
        refine ⟨7877511344661187321990511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5251674229774124881327007 7877511344661187321990511)
        ·
          refine ⟨11816267016991780982985767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7877511344661187321990511 11816267016991780982985767)
          ·
            refine ⟨17724400525487671474478651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11816267016991780982985767 17724400525487671474478651)
            ·
              refine ⟨26586600788231507211717977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17724400525487671474478651 26586600788231507211717977)
              ·
                refine ⟨19939950591173630408788483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26586600788231507211717977 19939950591173630408788483)
                ·
                  refine ⟨29909925886760445613182725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19939950591173630408788483 29909925886760445613182725)
                  ·
                    refine ⟨5608111103767583552471761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29909925886760445613182725 5608111103767583552471761)
                    ·
                      refine ⟨4206083327825687664353821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5608111103767583552471761 4206083327825687664353821)
                      ·
                        rfl

theorem cell23_8191318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_8191318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191318 prefixEnd_8191318 := by exact prefixLift 8191318
  have htrace : WordTrace (prefixWord ++ tailWord_8191318) baseStart_8191318 baseEnd_8191318 := by
    simpa [prefixWord, tailWord_8191318, baseEnd_8191318] using wordTrace_append hprefix tailTrace_8191318
  have hstable : (prefixWord ++ tailWord_8191318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191318).length < 2 ^ (prefixWord ++ tailWord_8191318).sum := by decide
  have hdescent : baseEnd_8191318 < baseStart_8191318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191340 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_8191340 : Nat := 118140960795 + 8191340 * 2 ^ 59
def prefixEnd_8191340 : Nat := 4983230072969 + 3 ^ 40 * 8191340 * 2
def baseEnd_8191340 : Nat := 4206094624400086578278719

theorem tailTrace_8191340 : CollatzResearch.WordTrace tailWord_8191340 prefixEnd_8191340 4206094624400086578278719 := by
  unfold tailWord_8191340
  simp only [CollatzResearch.WordTrace]
  refine ⟨149381357072090812169729737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199175142762787749559639649 149381357072090812169729737)
  ·
    refine ⟨112036017804068109127297303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149381357072090812169729737 112036017804068109127297303)
    ·
      refine ⟨168054026706102163690945955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112036017804068109127297303 168054026706102163690945955)
      ·
        refine ⟨252081040059153245536418933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168054026706102163690945955 252081040059153245536418933)
        ·
          refine ⟨23632597505545616769039275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252081040059153245536418933 23632597505545616769039275)
          ·
            refine ⟨35448896258318425153558913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23632597505545616769039275 35448896258318425153558913)
            ·
              refine ⟨26586672193738818865169185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35448896258318425153558913 26586672193738818865169185)
              ·
                refine ⟨19940004145304114148876889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26586672193738818865169185 19940004145304114148876889)
                ·
                  refine ⟨14955003108978085611657667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19940004145304114148876889 14955003108978085611657667)
                  ·
                    refine ⟨22432504663467128417486501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14955003108978085611657667 22432504663467128417486501)
                    ·
                      refine ⟨4206094624400086578278719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22432504663467128417486501 4206094624400086578278719)
                      ·
                        rfl

theorem cell23_8191340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_8191340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191340 prefixEnd_8191340 := by exact prefixLift 8191340
  have htrace : WordTrace (prefixWord ++ tailWord_8191340) baseStart_8191340 baseEnd_8191340 := by
    simpa [prefixWord, tailWord_8191340, baseEnd_8191340] using wordTrace_append hprefix tailTrace_8191340
  have hstable : (prefixWord ++ tailWord_8191340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191340).length < 2 ^ (prefixWord ++ tailWord_8191340).sum := by decide
  have hdescent : baseEnd_8191340 < baseStart_8191340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8191374 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_8191374 : Nat := 118140960795 + 8191374 * 2 ^ 59
def prefixEnd_8191374 : Nat := 4983230072969 + 3 ^ 40 * 8191374 * 2
def baseEnd_8191374 : Nat := 4206112082742339445253563

theorem tailTrace_8191374 : CollatzResearch.WordTrace tailWord_8191374 prefixEnd_8191374 4206112082742339445253563 := by
  unfold tailWord_8191374
  simp only [CollatzResearch.WordTrace]
  refine ⟨37345494278257306018274647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199175969484038965430798117 37345494278257306018274647)
  ·
    refine ⟨56018241417385959027411971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37345494278257306018274647 56018241417385959027411971)
    ·
      refine ⟨84027362126078938541117957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56018241417385959027411971 84027362126078938541117957)
      ·
        refine ⟨15755130398639800976459617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84027362126078938541117957 15755130398639800976459617)
        ·
          refine ⟨11816347798979850732344713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15755130398639800976459617 11816347798979850732344713)
          ·
            refine ⟨8862260849234888049258535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11816347798979850732344713 8862260849234888049258535)
            ·
              refine ⟨13293391273852332073887803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8862260849234888049258535 13293391273852332073887803)
              ·
                refine ⟨19940086910778498110831705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13293391273852332073887803 19940086910778498110831705)
                ·
                  refine ⟨14955065183083873583123779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19940086910778498110831705 14955065183083873583123779)
                  ·
                    refine ⟨22432597774625810374685669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14955065183083873583123779 22432597774625810374685669)
                    ·
                      refine ⟨4206112082742339445253563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22432597774625810374685669 4206112082742339445253563)
                      ·
                        rfl

theorem cell23_8191374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_8191374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8191374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8191374 prefixEnd_8191374 := by exact prefixLift 8191374
  have htrace : WordTrace (prefixWord ++ tailWord_8191374) baseStart_8191374 baseEnd_8191374 := by
    simpa [prefixWord, tailWord_8191374, baseEnd_8191374] using wordTrace_append hprefix tailTrace_8191374
  have hstable : (prefixWord ++ tailWord_8191374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8191374).length < 2 ^ (prefixWord ++ tailWord_8191374).sum := by decide
  have hdescent : baseEnd_8191374 < baseStart_8191374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8191374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
