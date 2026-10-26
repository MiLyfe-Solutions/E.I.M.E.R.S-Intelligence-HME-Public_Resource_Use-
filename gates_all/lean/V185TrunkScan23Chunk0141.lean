import V185TrunkScan23Chunk0140

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_833998 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2]
def baseStart_833998 : Nat := 118140960795 + 833998 * 2 ^ 59
def prefixEnd_833998 : Nat := 4983230072969 + 3 ^ 40 * 833998 * 2
def baseEnd_833998 : Nat := 428241838888533212689519

theorem tailTrace_833998 : CollatzResearch.WordTrace tailWord_833998 prefixEnd_833998 428241838888533212689519 := by
  unfold tailWord_833998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802300754071894545454831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20278937355050104242425765 3802300754071894545454831)
  ·
    refine ⟨5703451131107841818182247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3802300754071894545454831 5703451131107841818182247)
    ·
      refine ⟨8555176696661762727273371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5703451131107841818182247 8555176696661762727273371)
      ·
        refine ⟨12832765044992644090910057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8555176696661762727273371 12832765044992644090910057)
        ·
          refine ⟨9624573783744483068182543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12832765044992644090910057 9624573783744483068182543)
          ·
            refine ⟨14436860675616724602273815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9624573783744483068182543 14436860675616724602273815)
            ·
              refine ⟨21655291013425086903410723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14436860675616724602273815 21655291013425086903410723)
              ·
                refine ⟨32482936520137630355116085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21655291013425086903410723 32482936520137630355116085)
                ·
                  refine ⟨3045275298762902845792133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32482936520137630355116085 3045275298762902845792133)
                  ·
                    refine ⟨570989118518044283586025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3045275298762902845792133 570989118518044283586025)
                    ·
                      refine ⟨428241838888533212689519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 570989118518044283586025 428241838888533212689519)
                      ·
                        rfl

theorem cell23_833998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_833998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_833998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_833998 prefixEnd_833998 := by exact prefixLift 833998
  have htrace : WordTrace (prefixWord ++ tailWord_833998) baseStart_833998 baseEnd_833998 := by
    simpa [prefixWord, tailWord_833998, baseEnd_833998] using wordTrace_append hprefix tailTrace_833998
  have hstable : (prefixWord ++ tailWord_833998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833998).length < 2 ^ (prefixWord ++ tailWord_833998).sum := by decide
  have hdescent : baseEnd_833998 < baseStart_833998 := by decide
  rcases family_descends (prefixWord ++ tailWord_833998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834015 : List Nat := [1, 1, 2, 3, 3, 3, 2, 1, 1, 4, 2]
def baseStart_834015 : Nat := 118140960795 + 834015 * 2 ^ 59
def prefixEnd_834015 : Nat := 4983230072969 + 3 ^ 40 * 834015 * 2
def baseEnd_834015 : Nat := 428250568059659646176941

theorem tailTrace_834015 : CollatzResearch.WordTrace tailWord_834015 prefixEnd_834015 428250568059659646176941 := by
  unfold tailWord_834015
  simp only [CollatzResearch.WordTrace]
  refine ⟨30419026073513568267007499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20279350715675712178004999 30419026073513568267007499)
  ·
    refine ⟨45628539110270352400511249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30419026073513568267007499 45628539110270352400511249)
    ·
      refine ⟨34221404332702764300383437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45628539110270352400511249 34221404332702764300383437)
      ·
        refine ⟨12833026624763536612643789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34221404332702764300383437 12833026624763536612643789)
        ·
          refine ⟨4812384984286326229741421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12833026624763536612643789 4812384984286326229741421)
          ·
            refine ⟨1804644369107372336153033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4812384984286326229741421 1804644369107372336153033)
            ·
              refine ⟨1353483276830529252114775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1804644369107372336153033 1353483276830529252114775)
              ·
                refine ⟨2030224915245793878172163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1353483276830529252114775 2030224915245793878172163)
                ·
                  refine ⟨3045337372868690817258245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030224915245793878172163 3045337372868690817258245)
                  ·
                    refine ⟨571000757412879528235921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3045337372868690817258245 571000757412879528235921)
                    ·
                      refine ⟨428250568059659646176941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571000757412879528235921 428250568059659646176941)
                      ·
                        rfl

theorem cell23_834015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_834015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834015 prefixEnd_834015 := by exact prefixLift 834015
  have htrace : WordTrace (prefixWord ++ tailWord_834015) baseStart_834015 baseEnd_834015 := by
    simpa [prefixWord, tailWord_834015, baseEnd_834015] using wordTrace_append hprefix tailTrace_834015
  have hstable : (prefixWord ++ tailWord_834015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834015).length < 2 ^ (prefixWord ++ tailWord_834015).sum := by decide
  have hdescent : baseEnd_834015 < baseStart_834015 := by decide
  rcases family_descends (prefixWord ++ tailWord_834015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834031 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 3]
def baseStart_834031 : Nat := 118140960795 + 834031 * 2 ^ 59
def prefixEnd_834031 : Nat := 4983230072969 + 3 ^ 40 * 834031 * 2
def baseEnd_834031 : Nat := 428258783750131583576867

theorem tailTrace_834031 : CollatzResearch.WordTrace tailWord_834031 prefixEnd_834031 428258783750131583576867 := by
  unfold tailWord_834031
  simp only [CollatzResearch.WordTrace]
  refine ⟨30419609641455602999589947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20279739760970401999726631 30419609641455602999589947)
  ·
    refine ⟨45629414462183404499384921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30419609641455602999589947 45629414462183404499384921)
    ·
      refine ⟨34222060846637553374538691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45629414462183404499384921 34222060846637553374538691)
      ·
        refine ⟨51333091269956330061808037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34222060846637553374538691 51333091269956330061808037)
        ·
          refine ⟨9624954613116811886589007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51333091269956330061808037 9624954613116811886589007)
          ·
            refine ⟨14437431919675217829883511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9624954613116811886589007 14437431919675217829883511)
            ·
              refine ⟨21656147879512826744825267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14437431919675217829883511 21656147879512826744825267)
              ·
                refine ⟨32484221819269240117237901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21656147879512826744825267 32484221819269240117237901)
                ·
                  refine ⟨12181583182225965043964213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32484221819269240117237901 12181583182225965043964213)
                  ·
                    refine ⟨1142023423333684222871645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12181583182225965043964213 1142023423333684222871645)
                    ·
                      refine ⟨428258783750131583576867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1142023423333684222871645 428258783750131583576867)
                      ·
                        rfl

theorem cell23_834031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 3].length) (baseStart_834031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834031 prefixEnd_834031 := by exact prefixLift 834031
  have htrace : WordTrace (prefixWord ++ tailWord_834031) baseStart_834031 baseEnd_834031 := by
    simpa [prefixWord, tailWord_834031, baseEnd_834031] using wordTrace_append hprefix tailTrace_834031
  have hstable : (prefixWord ++ tailWord_834031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834031).length < 2 ^ (prefixWord ++ tailWord_834031).sum := by decide
  have hdescent : baseEnd_834031 < baseStart_834031 := by decide
  rcases family_descends (prefixWord ++ tailWord_834031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834049 : List Nat := [1, 2, 4, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_834049 : Nat := 118140960795 + 834049 * 2 ^ 59
def prefixEnd_834049 : Nat := 4983230072969 + 3 ^ 40 * 834049 * 2
def baseEnd_834049 : Nat := 428268026401912513151785

theorem tailTrace_834049 : CollatzResearch.WordTrace tailWord_834049 prefixEnd_834049 428268026401912513151785 := by
  unfold tailWord_834049
  simp only [CollatzResearch.WordTrace]
  refine ⟨30420266155390392073745201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20280177436926928049163467 30420266155390392073745201)
  ·
    refine ⟨22815199616542794055308901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30420266155390392073745201 22815199616542794055308901)
    ·
      refine ⟨4277849928101773885370419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22815199616542794055308901 4277849928101773885370419)
      ·
        refine ⟨6416774892152660828055629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4277849928101773885370419 6416774892152660828055629)
        ·
          refine ⟨2406290584557247810520861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6416774892152660828055629 2406290584557247810520861)
          ·
            refine ⟨902358969208967928945323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2406290584557247810520861 902358969208967928945323)
            ·
              refine ⟨1353538453813451893417985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902358969208967928945323 1353538453813451893417985)
              ·
                refine ⟨1015153840360088920063489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353538453813451893417985 1015153840360088920063489)
                ·
                  refine ⟨761365380270066690047617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1015153840360088920063489 761365380270066690047617)
                  ·
                    refine ⟨571024035202550017535713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 761365380270066690047617 571024035202550017535713)
                    ·
                      refine ⟨428268026401912513151785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571024035202550017535713 428268026401912513151785)
                      ·
                        rfl

theorem cell23_834049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_834049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834049 prefixEnd_834049 := by exact prefixLift 834049
  have htrace : WordTrace (prefixWord ++ tailWord_834049) baseStart_834049 baseEnd_834049 := by
    simpa [prefixWord, tailWord_834049, baseEnd_834049] using wordTrace_append hprefix tailTrace_834049
  have hstable : (prefixWord ++ tailWord_834049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834049).length < 2 ^ (prefixWord ++ tailWord_834049).sum := by decide
  have hdescent : baseEnd_834049 < baseStart_834049 := by decide
  rcases family_descends (prefixWord ++ tailWord_834049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834051 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 4, 5]
def baseStart_834051 : Nat := 118140960795 + 834051 * 2 ^ 59
def prefixEnd_834051 : Nat := 4983230072969 + 3 ^ 40 * 834051 * 2
def baseEnd_834051 : Nat := 142756351121073835108925

theorem tailTrace_834051 : CollatzResearch.WordTrace tailWord_834051 prefixEnd_834051 142756351121073835108925 := by
  unfold tailWord_834051
  simp only [CollatzResearch.WordTrace]
  refine ⟨30420339101383146415318007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20280226067588764276878671 30420339101383146415318007)
  ·
    refine ⟨45630508652074719622977011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30420339101383146415318007 45630508652074719622977011)
    ·
      refine ⟨68445762978112079434465517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45630508652074719622977011 68445762978112079434465517)
      ·
        refine ⟨25667161116792029787924569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68445762978112079434465517 25667161116792029787924569)
        ·
          refine ⟨19250370837594022340943427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25667161116792029787924569 19250370837594022340943427)
          ·
            refine ⟨28875556256391033511415141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19250370837594022340943427 28875556256391033511415141)
            ·
              refine ⟨5414166798073318783390339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28875556256391033511415141 5414166798073318783390339)
              ·
                refine ⟨8121250197109978175085509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5414166798073318783390339 8121250197109978175085509)
                ·
                  refine ⟨1522734411958120907828533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8121250197109978175085509 1522734411958120907828533)
                  ·
                    refine ⟨142756351121073835108925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1522734411958120907828533 142756351121073835108925)
                    ·
                      rfl

theorem cell23_834051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 5].length) (baseStart_834051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834051 prefixEnd_834051 := by exact prefixLift 834051
  have htrace : WordTrace (prefixWord ++ tailWord_834051) baseStart_834051 baseEnd_834051 := by
    simpa [prefixWord, tailWord_834051, baseEnd_834051] using wordTrace_append hprefix tailTrace_834051
  have hstable : (prefixWord ++ tailWord_834051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834051).length < 2 ^ (prefixWord ++ tailWord_834051).sum := by decide
  have hdescent : baseEnd_834051 < baseStart_834051 := by decide
  rcases family_descends (prefixWord ++ tailWord_834051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834081 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 2, 8]
def baseStart_834081 : Nat := 118140960795 + 834081 * 2 ^ 59
def prefixEnd_834081 : Nat := 4983230072969 + 3 ^ 40 * 834081 * 2
def baseEnd_834081 : Nat := 142761485927618795983879

theorem tailTrace_834081 : CollatzResearch.WordTrace tailWord_834081 prefixEnd_834081 142761485927618795983879 := by
  unfold tailWord_834081
  simp only [CollatzResearch.WordTrace]
  refine ⟨30421433291274461538910097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20280955527516307692606731 30421433291274461538910097)
  ·
    refine ⟨22816074968455846154182573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30421433291274461538910097 22816074968455846154182573)
    ·
      refine ⟨8556028113170942307818465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22816074968455846154182573 8556028113170942307818465)
      ·
        refine ⟨6417021084878206730863849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8556028113170942307818465 6417021084878206730863849)
        ·
          refine ⟨4812765813658655048147887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6417021084878206730863849 4812765813658655048147887)
          ·
            refine ⟨7219148720487982572221831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4812765813658655048147887 7219148720487982572221831)
            ·
              refine ⟨10828723080731973858332747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7219148720487982572221831 10828723080731973858332747)
              ·
                refine ⟨16243084621097960787499121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10828723080731973858332747 16243084621097960787499121)
                ·
                  refine ⟨12182313465823470590624341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16243084621097960787499121 12182313465823470590624341)
                  ·
                    refine ⟨142761485927618795983879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12182313465823470590624341 142761485927618795983879)
                    ·
                      rfl

theorem cell23_834081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_834081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834081 prefixEnd_834081 := by exact prefixLift 834081
  have htrace : WordTrace (prefixWord ++ tailWord_834081) baseStart_834081 baseEnd_834081 := by
    simpa [prefixWord, tailWord_834081, baseEnd_834081] using wordTrace_append hprefix tailTrace_834081
  have hstable : (prefixWord ++ tailWord_834081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834081).length < 2 ^ (prefixWord ++ tailWord_834081).sum := by decide
  have hdescent : baseEnd_834081 < baseStart_834081 := by decide
  rcases family_descends (prefixWord ++ tailWord_834081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834098 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_834098 : Nat := 118140960795 + 834098 * 2 ^ 59
def prefixEnd_834098 : Nat := 4983230072969 + 3 ^ 40 * 834098 * 2
def baseEnd_834098 : Nat := 142764395651327607146353

theorem tailTrace_834098 : CollatzResearch.WordTrace tailWord_834098 prefixEnd_834098 142764395651327607146353 := by
  unfold tailWord_834098
  simp only [CollatzResearch.WordTrace]
  refine ⟨7605513333053218360569737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20281368888141915628185965 7605513333053218360569737)
  ·
    refine ⟨5704134999789913770427303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7605513333053218360569737 5704134999789913770427303)
    ·
      refine ⟨8556202499684870655640955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5704134999789913770427303 8556202499684870655640955)
      ·
        refine ⟨12834303749527305983461433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8556202499684870655640955 12834303749527305983461433)
        ·
          refine ⟨9625727812145479487596075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12834303749527305983461433 9625727812145479487596075)
          ·
            refine ⟨14438591718218219231394113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9625727812145479487596075 14438591718218219231394113)
            ·
              refine ⟨10828943788663664423545585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14438591718218219231394113 10828943788663664423545585)
              ·
                refine ⟨8121707841497748317659189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10828943788663664423545585 8121707841497748317659189)
                ·
                  refine ⟨761410110140413904780549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8121707841497748317659189 761410110140413904780549)
                  ·
                    refine ⟨142764395651327607146353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 761410110140413904780549 142764395651327607146353)
                    ·
                      rfl

theorem cell23_834098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_834098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834098 prefixEnd_834098 := by exact prefixLift 834098
  have htrace : WordTrace (prefixWord ++ tailWord_834098) baseStart_834098 baseEnd_834098 := by
    simpa [prefixWord, tailWord_834098, baseEnd_834098] using wordTrace_append hprefix tailTrace_834098
  have hstable : (prefixWord ++ tailWord_834098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834098).length < 2 ^ (prefixWord ++ tailWord_834098).sum := by decide
  have hdescent : baseEnd_834098 < baseStart_834098 := by decide
  rcases family_descends (prefixWord ++ tailWord_834098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834111 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 8]
def baseStart_834111 : Nat := 118140960795 + 834111 * 2 ^ 59
def prefixEnd_834111 : Nat := 4983230072969 + 3 ^ 40 * 834111 * 2
def baseEnd_834111 : Nat := 47588873578054585619611

theorem tailTrace_834111 : CollatzResearch.WordTrace tailWord_834111 prefixEnd_834111 47588873578054585619611 := by
  unfold tailWord_834111
  simp only [CollatzResearch.WordTrace]
  refine ⟨30422527481165776662502187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20281684987443851108334791 30422527481165776662502187)
  ·
    refine ⟨45633791221748664993753281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30422527481165776662502187 45633791221748664993753281)
    ·
      refine ⟨34225343416311498745314961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45633791221748664993753281 34225343416311498745314961)
      ·
        refine ⟨25669007562233624058986221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34225343416311498745314961 25669007562233624058986221)
        ·
          refine ⟨9625877835837609022119833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25669007562233624058986221 9625877835837609022119833)
          ·
            refine ⟨7219408376878206766589875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9625877835837609022119833 7219408376878206766589875)
            ·
              refine ⟨10829112565317310149884813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7219408376878206766589875 10829112565317310149884813)
              ·
                refine ⟨4060917211993991306206805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10829112565317310149884813 4060917211993991306206805)
                ·
                  refine ⟨47588873578054585619611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4060917211993991306206805 47588873578054585619611)
                  ·
                    rfl

theorem cell23_834111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 8].length) (baseStart_834111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834111 prefixEnd_834111 := by exact prefixLift 834111
  have htrace : WordTrace (prefixWord ++ tailWord_834111) baseStart_834111 baseEnd_834111 := by
    simpa [prefixWord, tailWord_834111, baseEnd_834111] using wordTrace_append hprefix tailTrace_834111
  have hstable : (prefixWord ++ tailWord_834111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834111).length < 2 ^ (prefixWord ++ tailWord_834111).sum := by decide
  have hdescent : baseEnd_834111 < baseStart_834111 := by decide
  rcases family_descends (prefixWord ++ tailWord_834111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834115 : List Nat := [1, 1, 1, 3, 1, 2, 1, 8, 1, 4]
def baseStart_834115 : Nat := 118140960795 + 834115 * 2 ^ 59
def prefixEnd_834115 : Nat := 4983230072969 + 3 ^ 40 * 834115 * 2
def baseEnd_834115 : Nat := 142767305375036418308827

theorem tailTrace_834115 : CollatzResearch.WordTrace tailWord_834115 prefixEnd_834115 142767305375036418308827 := by
  unfold tailWord_834115
  simp only [CollatzResearch.WordTrace]
  refine ⟨30422673373151285345647799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20281782248767523563765199 30422673373151285345647799)
  ·
    refine ⟨45634010059726928018471699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30422673373151285345647799 45634010059726928018471699)
    ·
      refine ⟨68451015089590392027707549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45634010059726928018471699 68451015089590392027707549)
      ·
        refine ⟨25669130658596397010390331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68451015089590392027707549 25669130658596397010390331)
        ·
          refine ⟨38503695987894595515585497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25669130658596397010390331 38503695987894595515585497)
          ·
            refine ⟨28877771990920946636689123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38503695987894595515585497 28877771990920946636689123)
            ·
              refine ⟨43316657986381419955033685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28877771990920946636689123 43316657986381419955033685)
              ·
                refine ⟨507617085777907265098051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 43316657986381419955033685 507617085777907265098051)
                ·
                  refine ⟨761425628666860897647077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507617085777907265098051 761425628666860897647077)
                  ·
                    refine ⟨142767305375036418308827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 761425628666860897647077 142767305375036418308827)
                    ·
                      rfl

theorem cell23_834115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 1, 4].length) (baseStart_834115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834115 prefixEnd_834115 := by exact prefixLift 834115
  have htrace : WordTrace (prefixWord ++ tailWord_834115) baseStart_834115 baseEnd_834115 := by
    simpa [prefixWord, tailWord_834115, baseEnd_834115] using wordTrace_append hprefix tailTrace_834115
  have hstable : (prefixWord ++ tailWord_834115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834115).length < 2 ^ (prefixWord ++ tailWord_834115).sum := by decide
  have hdescent : baseEnd_834115 < baseStart_834115 := by decide
  rcases family_descends (prefixWord ++ tailWord_834115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834206 : List Nat := [4, 3, 1, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_834206 : Nat := 118140960795 + 834206 * 2 ^ 59
def prefixEnd_834206 : Nat := 4983230072969 + 3 ^ 40 * 834206 * 2
def baseEnd_834206 : Nat := 428348642864668398888563

theorem tailTrace_834206 : CollatzResearch.WordTrace tailWord_834206 prefixEnd_834206 428348642864668398888563 := by
  unfold tailWord_834206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3803249051977700985901309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20283994943881071924806981 3803249051977700985901309)
  ·
    refine ⟨1426218394491637869712991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3803249051977700985901309 1426218394491637869712991)
    ·
      refine ⟨2139327591737456804569487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426218394491637869712991 2139327591737456804569487)
      ·
        refine ⟨3208991387606185206854231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139327591737456804569487 3208991387606185206854231)
        ·
          refine ⟨4813487081409277810281347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208991387606185206854231 4813487081409277810281347)
          ·
            refine ⟨7220230622113916715422021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4813487081409277810281347 7220230622113916715422021)
            ·
              refine ⟨1353793241646359384141629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7220230622113916715422021 1353793241646359384141629)
              ·
                refine ⟨507672465617384769053111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1353793241646359384141629 507672465617384769053111)
                ·
                  refine ⟨761508698426077153579667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507672465617384769053111 761508698426077153579667)
                  ·
                    refine ⟨1142263047639115730369501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 761508698426077153579667 1142263047639115730369501)
                    ·
                      refine ⟨428348642864668398888563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1142263047639115730369501 428348642864668398888563)
                      ·
                        rfl

theorem cell23_834206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_834206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834206 prefixEnd_834206 := by exact prefixLift 834206
  have htrace : WordTrace (prefixWord ++ tailWord_834206) baseStart_834206 baseEnd_834206 := by
    simpa [prefixWord, tailWord_834206, baseEnd_834206] using wordTrace_append hprefix tailTrace_834206
  have hstable : (prefixWord ++ tailWord_834206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834206).length < 2 ^ (prefixWord ++ tailWord_834206).sum := by decide
  have hdescent : baseEnd_834206 < baseStart_834206 := by decide
  rcases family_descends (prefixWord ++ tailWord_834206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834209 : List Nat := [1, 2, 3, 3, 3, 2, 2, 1, 1, 5]
def baseStart_834209 : Nat := 118140960795 + 834209 * 2 ^ 59
def prefixEnd_834209 : Nat := 4983230072969 + 3 ^ 40 * 834209 * 2
def baseEnd_834209 : Nat := 142783394435543962383683

theorem tailTrace_834209 : CollatzResearch.WordTrace tailWord_834209 prefixEnd_834209 142783394435543962383683 := by
  unfold tailWord_834209
  simp only [CollatzResearch.WordTrace]
  refine ⟨30426101834810739399569681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20284067889873826266379787 30426101834810739399569681)
  ·
    refine ⟨22819576376108054549677261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30426101834810739399569681 22819576376108054549677261)
    ·
      refine ⟨8557341141040520456128973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22819576376108054549677261 8557341141040520456128973)
      ·
        refine ⟨3209002927890195171048365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8557341141040520456128973 3209002927890195171048365)
        ·
          refine ⟨1203376097958823189143137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3209002927890195171048365 1203376097958823189143137)
          ·
            refine ⟨902532073469117391857353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1203376097958823189143137 902532073469117391857353)
            ·
              refine ⟨676899055101838043893015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902532073469117391857353 676899055101838043893015)
              ·
                refine ⟨1015348582652757065839523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676899055101838043893015 1015348582652757065839523)
                ·
                  refine ⟨1523022873979135598759285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015348582652757065839523 1523022873979135598759285)
                  ·
                    refine ⟨142783394435543962383683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1523022873979135598759285 142783394435543962383683)
                    ·
                      rfl

theorem cell23_834209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_834209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834209 prefixEnd_834209 := by exact prefixLift 834209
  have htrace : WordTrace (prefixWord ++ tailWord_834209) baseStart_834209 baseEnd_834209 := by
    simpa [prefixWord, tailWord_834209, baseEnd_834209] using wordTrace_append hprefix tailTrace_834209
  have hstable : (prefixWord ++ tailWord_834209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834209).length < 2 ^ (prefixWord ++ tailWord_834209).sum := by decide
  have hdescent : baseEnd_834209 < baseStart_834209 := by decide
  rcases family_descends (prefixWord ++ tailWord_834209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834212 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 5, 2, 2]
def baseStart_834212 : Nat := 118140960795 + 834212 * 2 ^ 59
def prefixEnd_834212 : Nat := 4983230072969 + 3 ^ 40 * 834212 * 2
def baseEnd_834212 : Nat := 428351723748595375413535

theorem tailTrace_834212 : CollatzResearch.WordTrace tailWord_834212 prefixEnd_834212 428351723748595375413535 := by
  unfold tailWord_834212
  simp only [CollatzResearch.WordTrace]
  refine ⟨15213105626899935455964445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20284140835866580607952593 15213105626899935455964445)
  ·
    refine ⟨5704914610087475795986667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15213105626899935455964445 5704914610087475795986667)
    ·
      refine ⟨8557371915131213693980001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5704914610087475795986667 8557371915131213693980001)
      ·
        refine ⟨6418028936348410270485001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8557371915131213693980001 6418028936348410270485001)
        ·
          refine ⟨4813521702261307702863751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6418028936348410270485001 4813521702261307702863751)
          ·
            refine ⟨7220282553391961554295627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4813521702261307702863751 7220282553391961554295627)
            ·
              refine ⟨10830423830087942331443441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7220282553391961554295627 10830423830087942331443441)
              ·
                refine ⟨8122817872565956748582581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10830423830087942331443441 8122817872565956748582581)
                ·
                  refine ⟨761514175553058445179617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8122817872565956748582581 761514175553058445179617)
                  ·
                    refine ⟨571135631664793833884713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 761514175553058445179617 571135631664793833884713)
                    ·
                      refine ⟨428351723748595375413535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571135631664793833884713 428351723748595375413535)
                      ·
                        rfl

theorem cell23_834212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_834212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834212 prefixEnd_834212 := by exact prefixLift 834212
  have htrace : WordTrace (prefixWord ++ tailWord_834212) baseStart_834212 baseEnd_834212 := by
    simpa [prefixWord, tailWord_834212, baseEnd_834212] using wordTrace_append hprefix tailTrace_834212
  have hstable : (prefixWord ++ tailWord_834212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834212).length < 2 ^ (prefixWord ++ tailWord_834212).sum := by decide
  have hdescent : baseEnd_834212 < baseStart_834212 := by decide
  rcases family_descends (prefixWord ++ tailWord_834212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834229 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_834229 : Nat := 118140960795 + 834229 * 2 ^ 59
def prefixEnd_834229 : Nat := 4983230072969 + 3 ^ 40 * 834229 * 2
def baseEnd_834229 : Nat := 428360452919721808900957

theorem tailTrace_834229 : CollatzResearch.WordTrace tailWord_834229 prefixEnd_834229 428360452919721808900957 := by
  unfold tailWord_834229
  simp only [CollatzResearch.WordTrace]
  refine ⟨30426831294738282815297741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20284554196492188543531827 30426831294738282815297741)
  ·
    refine ⟨11410061735526856055736653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30426831294738282815297741 11410061735526856055736653)
    ·
      refine ⟨4278773150822571020901245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11410061735526856055736653 4278773150822571020901245)
      ·
        refine ⟨1604539931558464132837967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4278773150822571020901245 1604539931558464132837967)
        ·
          refine ⟨2406809897337696199256951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604539931558464132837967 2406809897337696199256951)
          ·
            refine ⟨3610214846006544298885427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406809897337696199256951 3610214846006544298885427)
            ·
              refine ⟨5415322269009816448328141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3610214846006544298885427 5415322269009816448328141)
              ·
                refine ⟨2030745850878681168123053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5415322269009816448328141 2030745850878681168123053)
                ·
                  refine ⟨761529694079505438046145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2030745850878681168123053 761529694079505438046145)
                  ·
                    refine ⟨571147270559629078534609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 761529694079505438046145 571147270559629078534609)
                    ·
                      refine ⟨428360452919721808900957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571147270559629078534609 428360452919721808900957)
                      ·
                        rfl

theorem cell23_834229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_834229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834229 prefixEnd_834229 := by exact prefixLift 834229
  have htrace : WordTrace (prefixWord ++ tailWord_834229) baseStart_834229 baseEnd_834229 := by
    simpa [prefixWord, tailWord_834229, baseEnd_834229] using wordTrace_append hprefix tailTrace_834229
  have hstable : (prefixWord ++ tailWord_834229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834229).length < 2 ^ (prefixWord ++ tailWord_834229).sum := by decide
  have hdescent : baseEnd_834229 < baseStart_834229 := by decide
  rcases family_descends (prefixWord ++ tailWord_834229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834245 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 8, 1, 3]
def baseStart_834245 : Nat := 118140960795 + 834245 * 2 ^ 59
def prefixEnd_834245 : Nat := 4983230072969 + 3 ^ 40 * 834245 * 2
def baseEnd_834245 : Nat := 428368668610193746300883

theorem tailTrace_834245 : CollatzResearch.WordTrace tailWord_834245 prefixEnd_834245 428368668610193746300883 := by
  unfold tailWord_834245
  simp only [CollatzResearch.WordTrace]
  refine ⟨30427414862680317547880189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20284943241786878365253459 30427414862680317547880189)
  ·
    refine ⟨11410280573505119080455071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30427414862680317547880189 11410280573505119080455071)
    ·
      refine ⟨17115420860257678620682607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11410280573505119080455071 17115420860257678620682607)
      ·
        refine ⟨25673131290386517931023911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17115420860257678620682607 25673131290386517931023911)
        ·
          refine ⟨38509696935579776896535867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25673131290386517931023911 38509696935579776896535867)
          ·
            refine ⟨57764545403369665344803801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38509696935579776896535867 57764545403369665344803801)
            ·
              refine ⟨43323409052527249008602851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57764545403369665344803801 43323409052527249008602851)
              ·
                refine ⟨64985113578790873512904277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43323409052527249008602851 64985113578790873512904277)
                ·
                  refine ⟨761544299751455548979347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 64985113578790873512904277 761544299751455548979347)
                  ·
                    refine ⟨1142316449627183323469021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 761544299751455548979347 1142316449627183323469021)
                    ·
                      refine ⟨428368668610193746300883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1142316449627183323469021 428368668610193746300883)
                      ·
                        rfl

theorem cell23_834245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_834245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834245 prefixEnd_834245 := by exact prefixLift 834245
  have htrace : WordTrace (prefixWord ++ tailWord_834245) baseStart_834245 baseEnd_834245 := by
    simpa [prefixWord, tailWord_834245, baseEnd_834245] using wordTrace_append hprefix tailTrace_834245
  have hstable : (prefixWord ++ tailWord_834245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834245).length < 2 ^ (prefixWord ++ tailWord_834245).sum := by decide
  have hdescent : baseEnd_834245 < baseStart_834245 := by decide
  rcases family_descends (prefixWord ++ tailWord_834245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834252 : List Nat := [2, 2, 1, 5, 1, 3, 2, 7]
def baseStart_834252 : Nat := 118140960795 + 834252 * 2 ^ 59
def prefixEnd_834252 : Nat := 4983230072969 + 3 ^ 40 * 834252 * 2
def baseEnd_834252 : Nat := 15865639369436119219013

theorem tailTrace_834252 : CollatzResearch.WordTrace tailWord_834252 prefixEnd_834252 15865639369436119219013 := by
  unfold tailWord_834252
  simp only [CollatzResearch.WordTrace]
  refine ⟨15213835086827478871692505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20285113449103305162256673 15213835086827478871692505)
  ·
    refine ⟨11410376315120609153769379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15213835086827478871692505 11410376315120609153769379)
    ·
      refine ⟨17115564472680913730654069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11410376315120609153769379 17115564472680913730654069)
      ·
        refine ⟨1604584169313835662248819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17115564472680913730654069 1604584169313835662248819)
        ·
          refine ⟨2406876253970753493373229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604584169313835662248819 2406876253970753493373229)
          ·
            refine ⟨902578595239032560014961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2406876253970753493373229 902578595239032560014961)
            ·
              refine ⟨676933946429274420011221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902578595239032560014961 676933946429274420011221)
              ·
                refine ⟨15865639369436119219013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 676933946429274420011221 15865639369436119219013)
                ·
                  rfl

theorem cell23_834252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 7].length) (baseStart_834252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834252 prefixEnd_834252 := by exact prefixLift 834252
  have htrace : WordTrace (prefixWord ++ tailWord_834252) baseStart_834252 baseEnd_834252 := by
    simpa [prefixWord, tailWord_834252, baseEnd_834252] using wordTrace_append hprefix tailTrace_834252
  have hstable : (prefixWord ++ tailWord_834252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834252).length < 2 ^ (prefixWord ++ tailWord_834252).sum := by decide
  have hdescent : baseEnd_834252 < baseStart_834252 := by decide
  rcases family_descends (prefixWord ++ tailWord_834252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834285 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_834285 : Nat := 118140960795 + 834285 * 2 ^ 59
def prefixEnd_834285 : Nat := 4983230072969 + 3 ^ 40 * 834285 * 2
def baseEnd_834285 : Nat := 428389207836373589800699

theorem tailTrace_834285 : CollatzResearch.WordTrace tailWord_834285 prefixEnd_834285 428389207836373589800699 := by
  unfold tailWord_834285
  simp only [CollatzResearch.WordTrace]
  refine ⟨30428873782535404379336309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20285915855023602919557539 30428873782535404379336309)
  ·
    refine ⟨2852706917112694160562779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30428873782535404379336309 2852706917112694160562779)
    ·
      refine ⟨4279060375669041240844169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2852706917112694160562779 4279060375669041240844169)
      ·
        refine ⟨3209295281751780930633127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4279060375669041240844169 3209295281751780930633127)
        ·
          refine ⟨4813942922627671395949691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3209295281751780930633127 4813942922627671395949691)
          ·
            refine ⟨7220914383941507093924537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4813942922627671395949691 7220914383941507093924537)
            ·
              refine ⟨5415685787956130320443403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7220914383941507093924537 5415685787956130320443403)
              ·
                refine ⟨8123528681934195480665105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5415685787956130320443403 8123528681934195480665105)
                ·
                  refine ⟨6092646511450646610498829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8123528681934195480665105 6092646511450646610498829)
                  ·
                    refine ⟨2284742441793992478937061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6092646511450646610498829 2284742441793992478937061)
                    ·
                      refine ⟨428389207836373589800699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2284742441793992478937061 428389207836373589800699)
                      ·
                        rfl

theorem cell23_834285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_834285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834285 prefixEnd_834285 := by exact prefixLift 834285
  have htrace : WordTrace (prefixWord ++ tailWord_834285) baseStart_834285 baseEnd_834285 := by
    simpa [prefixWord, tailWord_834285, baseEnd_834285] using wordTrace_append hprefix tailTrace_834285
  have hstable : (prefixWord ++ tailWord_834285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834285).length < 2 ^ (prefixWord ++ tailWord_834285).sum := by decide
  have hdescent : baseEnd_834285 < baseStart_834285 := by decide
  rcases family_descends (prefixWord ++ tailWord_834285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834288 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 5]
def baseStart_834288 : Nat := 118140960795 + 834288 * 2 ^ 59
def prefixEnd_834288 : Nat := 4983230072969 + 3 ^ 40 * 834288 * 2
def baseEnd_834288 : Nat := 428390748278337078063185

theorem tailTrace_834288 : CollatzResearch.WordTrace tailWord_834288 prefixEnd_834288 428390748278337078063185 := by
  unfold tailWord_834288
  simp only [CollatzResearch.WordTrace]
  refine ⟨15214491600762267945847759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20285988801016357261130345 15214491600762267945847759)
  ·
    refine ⟨22821737401143401918771639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15214491600762267945847759 22821737401143401918771639)
    ·
      refine ⟨34232606101715102878157459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22821737401143401918771639 34232606101715102878157459)
      ·
        refine ⟨51348909152572654317236189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34232606101715102878157459 51348909152572654317236189)
        ·
          refine ⟨19255840932214745368963571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51348909152572654317236189 19255840932214745368963571)
          ·
            refine ⟨28883761398322118053445357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19255840932214745368963571 28883761398322118053445357)
            ·
              refine ⟨10831410524370794270042009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28883761398322118053445357 10831410524370794270042009)
              ·
                refine ⟨8123557893278095702531507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10831410524370794270042009 8123557893278095702531507)
                ·
                  refine ⟨12185336839917143553797261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8123557893278095702531507 12185336839917143553797261)
                  ·
                    refine ⟨4569501314968928832673973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12185336839917143553797261 4569501314968928832673973)
                    ·
                      refine ⟨428390748278337078063185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4569501314968928832673973 428390748278337078063185)
                      ·
                        rfl

theorem cell23_834288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_834288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834288 prefixEnd_834288 := by exact prefixLift 834288
  have htrace : WordTrace (prefixWord ++ tailWord_834288) baseStart_834288 baseEnd_834288 := by
    simpa [prefixWord, tailWord_834288, baseEnd_834288] using wordTrace_append hprefix tailTrace_834288
  have hstable : (prefixWord ++ tailWord_834288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834288).length < 2 ^ (prefixWord ++ tailWord_834288).sum := by decide
  have hdescent : baseEnd_834288 < baseStart_834288 := by decide
  rcases family_descends (prefixWord ++ tailWord_834288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834306 : List Nat := [3, 4, 1, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_834306 : Nat := 118140960795 + 834306 * 2 ^ 59
def prefixEnd_834306 : Nat := 4983230072969 + 3 ^ 40 * 834306 * 2
def baseEnd_834306 : Nat := 428399990930118007638103

theorem tailTrace_834306 : CollatzResearch.WordTrace tailWord_834306 prefixEnd_834306 428399990930118007638103 := by
  unfold tailWord_834306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7607409928864831241462693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20286426476972883310567181 7607409928864831241462693)
  ·
    refine ⟨1426389361662155857774255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7607409928864831241462693 1426389361662155857774255)
    ·
      refine ⟨2139584042493233786661383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426389361662155857774255 2139584042493233786661383)
      ·
        refine ⟨3209376063739850679992075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139584042493233786661383 3209376063739850679992075)
        ·
          refine ⟨4814064095609776019988113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3209376063739850679992075 4814064095609776019988113)
          ·
            refine ⟨3610548071707332014991085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4814064095609776019988113 3610548071707332014991085)
            ·
              refine ⟨1353955526890249505621657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3610548071707332014991085 1353955526890249505621657)
              ·
                refine ⟨1015466645167687129216243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353955526890249505621657 1015466645167687129216243)
                ·
                  refine ⟨1523199967751530693824365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015466645167687129216243 1523199967751530693824365)
                  ·
                    refine ⟨571199987906824010184137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1523199967751530693824365 571199987906824010184137)
                    ·
                      refine ⟨428399990930118007638103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571199987906824010184137 428399990930118007638103)
                      ·
                        rfl

theorem cell23_834306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_834306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834306 prefixEnd_834306 := by exact prefixLift 834306
  have htrace : WordTrace (prefixWord ++ tailWord_834306) baseStart_834306 baseEnd_834306 := by
    simpa [prefixWord, tailWord_834306, baseEnd_834306] using wordTrace_append hprefix tailTrace_834306
  have hstable : (prefixWord ++ tailWord_834306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834306).length < 2 ^ (prefixWord ++ tailWord_834306).sum := by decide
  have hdescent : baseEnd_834306 < baseStart_834306 := by decide
  rcases family_descends (prefixWord ++ tailWord_834306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834336 : List Nat := [2, 1, 1, 5, 1, 3, 2, 2, 2, 2, 2]
def baseStart_834336 : Nat := 118140960795 + 834336 * 2 ^ 59
def prefixEnd_834336 : Nat := 4983230072969 + 3 ^ 40 * 834336 * 2
def baseEnd_834336 : Nat := 428415395349752890262965

theorem tailTrace_834336 : CollatzResearch.WordTrace tailWord_834336 prefixEnd_834336 428415395349752890262965 := by
  unfold tailWord_834336
  simp only [CollatzResearch.WordTrace]
  refine ⟨15215366952675320044721431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20287155936900426726295241 15215366952675320044721431)
  ·
    refine ⟨22823050429012980067082147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15215366952675320044721431 22823050429012980067082147)
    ·
      refine ⟨34234575643519470100623221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22823050429012980067082147 34234575643519470100623221)
      ·
        refine ⟨3209491466579950321933427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34234575643519470100623221 3209491466579950321933427)
        ·
          refine ⟨4814237199869925482900141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3209491466579950321933427 4814237199869925482900141)
          ·
            refine ⟨1805338949951222056087553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4814237199869925482900141 1805338949951222056087553)
            ·
              refine ⟨1354004212463416542065665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1805338949951222056087553 1354004212463416542065665)
              ·
                refine ⟨1015503159347562406549249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354004212463416542065665 1015503159347562406549249)
                ·
                  refine ⟨761627369510671804911937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1015503159347562406549249 761627369510671804911937)
                  ·
                    refine ⟨571220527133003853683953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 761627369510671804911937 571220527133003853683953)
                    ·
                      refine ⟨428415395349752890262965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571220527133003853683953 428415395349752890262965)
                      ·
                        rfl

theorem cell23_834336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_834336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834336 prefixEnd_834336 := by exact prefixLift 834336
  have htrace : WordTrace (prefixWord ++ tailWord_834336) baseStart_834336 baseEnd_834336 := by
    simpa [prefixWord, tailWord_834336, baseEnd_834336] using wordTrace_append hprefix tailTrace_834336
  have hstable : (prefixWord ++ tailWord_834336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834336).length < 2 ^ (prefixWord ++ tailWord_834336).sum := by decide
  have hdescent : baseEnd_834336 < baseStart_834336 := by decide
  rcases family_descends (prefixWord ++ tailWord_834336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834415 : List Nat := [1, 1, 2, 1, 3, 1, 1, 7, 6]
def baseStart_834415 : Nat := 118140960795 + 834415 * 2 ^ 59
def prefixEnd_834415 : Nat := 4983230072969 + 3 ^ 40 * 834415 * 2
def baseEnd_834415 : Nat := 47606217813495342352789

theorem tailTrace_834415 : CollatzResearch.WordTrace tailWord_834415 prefixEnd_834415 47606217813495342352789 := by
  unfold tailWord_834415
  simp only [CollatzResearch.WordTrace]
  refine ⟨30433615272064436581568699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20289076848042957721045799 30433615272064436581568699)
  ·
    refine ⟨45650422908096654872353049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30433615272064436581568699 45650422908096654872353049)
    ·
      refine ⟨34237817181072491154264787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45650422908096654872353049 34237817181072491154264787)
      ·
        refine ⟨51356725771608736731397181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34237817181072491154264787 51356725771608736731397181)
        ·
          refine ⟨19258772164353276274273943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51356725771608736731397181 19258772164353276274273943)
          ·
            refine ⟨28888158246529914411410915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19258772164353276274273943 28888158246529914411410915)
            ·
              refine ⟨43332237369794871617116373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28888158246529914411410915 43332237369794871617116373)
              ·
                refine ⟨1015599313354567303526165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43332237369794871617116373 1015599313354567303526165)
                ·
                  refine ⟨47606217813495342352789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1015599313354567303526165 47606217813495342352789)
                  ·
                    rfl

theorem cell23_834415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 6].length) (baseStart_834415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834415 prefixEnd_834415 := by exact prefixLift 834415
  have htrace : WordTrace (prefixWord ++ tailWord_834415) baseStart_834415 baseEnd_834415 := by
    simpa [prefixWord, tailWord_834415, baseEnd_834415] using wordTrace_append hprefix tailTrace_834415
  have hstable : (prefixWord ++ tailWord_834415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834415).length < 2 ^ (prefixWord ++ tailWord_834415).sum := by decide
  have hdescent : baseEnd_834415 < baseStart_834415 := by decide
  rcases family_descends (prefixWord ++ tailWord_834415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834466 : List Nat := [3, 3, 1, 2, 2, 3, 2, 1, 6]
def baseStart_834466 : Nat := 118140960795 + 834466 * 2 ^ 59
def prefixEnd_834466 : Nat := 4983230072969 + 3 ^ 40 * 834466 * 2
def baseEnd_834466 : Nat := 47609127537204153515263

theorem tailTrace_834466 : CollatzResearch.WordTrace tailWord_834466 prefixEnd_834466 47609127537204153515263 := by
  unfold tailWord_834466
  simp only [CollatzResearch.WordTrace]
  refine ⟨7608868848719918072918813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20290316929919781527783501 7608868848719918072918813)
  ·
    refine ⟨2853325818269969277344555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7608868848719918072918813 2853325818269969277344555)
    ·
      refine ⟨4279988727404953916016833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2853325818269969277344555 4279988727404953916016833)
      ·
        refine ⟨3209991545553715437012625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4279988727404953916016833 3209991545553715437012625)
        ·
          refine ⟨2407493659165286577759469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3209991545553715437012625 2407493659165286577759469)
          ·
            refine ⟨902810122186982466659801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2407493659165286577759469 902810122186982466659801)
            ·
              refine ⟨677107591640236849994851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902810122186982466659801 677107591640236849994851)
              ·
                refine ⟨1015661387460355274992277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677107591640236849994851 1015661387460355274992277)
                ·
                  refine ⟨47609127537204153515263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1015661387460355274992277 47609127537204153515263)
                  ·
                    rfl

theorem cell23_834466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_834466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834466 prefixEnd_834466 := by exact prefixLift 834466
  have htrace : WordTrace (prefixWord ++ tailWord_834466) baseStart_834466 baseEnd_834466 := by
    simpa [prefixWord, tailWord_834466, baseEnd_834466] using wordTrace_append hprefix tailTrace_834466
  have hstable : (prefixWord ++ tailWord_834466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834466).length < 2 ^ (prefixWord ++ tailWord_834466).sum := by decide
  have hdescent : baseEnd_834466 < baseStart_834466 := by decide
  rcases family_descends (prefixWord ++ tailWord_834466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834495 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 6]
def baseStart_834495 : Nat := 118140960795 + 834495 * 2 ^ 59
def prefixEnd_834495 : Nat := 4983230072969 + 3 ^ 40 * 834495 * 2
def baseEnd_834495 : Nat := 428497038773817768174733

theorem tailTrace_834495 : CollatzResearch.WordTrace tailWord_834495 prefixEnd_834495 428497038773817768174733 := by
  unfold tailWord_834495
  simp only [CollatzResearch.WordTrace]
  refine ⟨30436533111774610244480939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20291022074516406829653959 30436533111774610244480939)
  ·
    refine ⟨45654799667661915366721409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30436533111774610244480939 45654799667661915366721409)
    ·
      refine ⟨34241099750746436525041057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45654799667661915366721409 34241099750746436525041057)
      ·
        refine ⟨25680824813059827393780793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34241099750746436525041057 25680824813059827393780793)
        ·
          refine ⟨19260618609794870545335595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25680824813059827393780793 19260618609794870545335595)
          ·
            refine ⟨28890927914692305818003393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19260618609794870545335595 28890927914692305818003393)
            ·
              refine ⟨21668195936019229363502545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28890927914692305818003393 21668195936019229363502545)
              ·
                refine ⟨16251146952014422022626909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21668195936019229363502545 16251146952014422022626909)
                ·
                  refine ⟨6094180107005408258485091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16251146952014422022626909 6094180107005408258485091)
                  ·
                    refine ⟨9141270160508112387727637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6094180107005408258485091 9141270160508112387727637)
                    ·
                      refine ⟨428497038773817768174733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9141270160508112387727637 428497038773817768174733)
                      ·
                        rfl

theorem cell23_834495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_834495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834495 prefixEnd_834495 := by exact prefixLift 834495
  have htrace : WordTrace (prefixWord ++ tailWord_834495) baseStart_834495 baseEnd_834495 := by
    simpa [prefixWord, tailWord_834495, baseEnd_834495] using wordTrace_append hprefix tailTrace_834495
  have hstable : (prefixWord ++ tailWord_834495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834495).length < 2 ^ (prefixWord ++ tailWord_834495).sum := by decide
  have hdescent : baseEnd_834495 < baseStart_834495 := by decide
  rcases family_descends (prefixWord ++ tailWord_834495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834499 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 5, 2, 2]
def baseStart_834499 : Nat := 118140960795 + 834499 * 2 ^ 59
def prefixEnd_834499 : Nat := 4983230072969 + 3 ^ 40 * 834499 * 2
def baseEnd_834499 : Nat := 428499092696435752524715

theorem tailTrace_834499 : CollatzResearch.WordTrace tailWord_834499 prefixEnd_834499 428499092696435752524715 := by
  unfold tailWord_834499
  simp only [CollatzResearch.WordTrace]
  refine ⟨30436679003760118927626551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20291119335840079285084367 30436679003760118927626551)
  ·
    refine ⟨45655018505640178391439827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30436679003760118927626551 45655018505640178391439827)
    ·
      refine ⟨68482527758460267587159741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45655018505640178391439827 68482527758460267587159741)
      ·
        refine ⟨25680947909422600345184903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68482527758460267587159741 25680947909422600345184903)
        ·
          refine ⟨38521421864133900517777355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25680947909422600345184903 38521421864133900517777355)
          ·
            refine ⟨57782132796200850776666033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38521421864133900517777355 57782132796200850776666033)
            ·
              refine ⟨43336599597150638082499525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57782132796200850776666033 43336599597150638082499525)
              ·
                refine ⟨8125612424465744640468661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43336599597150638082499525 8125612424465744640468661)
                ·
                  refine ⟨761776164793663560043937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8125612424465744640468661 761776164793663560043937)
                  ·
                    refine ⟨571332123595247670032953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 761776164793663560043937 571332123595247670032953)
                    ·
                      refine ⟨428499092696435752524715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571332123595247670032953 428499092696435752524715)
                      ·
                        rfl

theorem cell23_834499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 2, 2].length) (baseStart_834499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834499 prefixEnd_834499 := by exact prefixLift 834499
  have htrace : WordTrace (prefixWord ++ tailWord_834499) baseStart_834499 baseEnd_834499 := by
    simpa [prefixWord, tailWord_834499, baseEnd_834499] using wordTrace_append hprefix tailTrace_834499
  have hstable : (prefixWord ++ tailWord_834499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834499).length < 2 ^ (prefixWord ++ tailWord_834499).sum := by decide
  have hdescent : baseEnd_834499 < baseStart_834499 := by decide
  rcases family_descends (prefixWord ++ tailWord_834499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834510 : List Nat := [4, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3]
def baseStart_834510 : Nat := 118140960795 + 834510 * 2 ^ 59
def prefixEnd_834510 : Nat := 4983230072969 + 3 ^ 40 * 834510 * 2
def baseEnd_834510 : Nat := 428504740983635209487165

theorem tailTrace_834510 : CollatzResearch.WordTrace tailWord_834510 prefixEnd_834510 428504740983635209487165 := by
  unfold tailWord_834510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3804635025840033475784623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20291386804480178537517989 3804635025840033475784623)
  ·
    refine ⟨5706952538760050213676935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3804635025840033475784623 5706952538760050213676935)
    ·
      refine ⟨8560428808140075320515403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5706952538760050213676935 8560428808140075320515403)
      ·
        refine ⟨12840643212210112980773105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8560428808140075320515403 12840643212210112980773105)
        ·
          refine ⟨9630482409157584735579829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12840643212210112980773105 9630482409157584735579829)
          ·
            refine ⟨902857725858523568960609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9630482409157584735579829 902857725858523568960609)
            ·
              refine ⟨677143294393892676720457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902857725858523568960609 677143294393892676720457)
              ·
                refine ⟨507857470795419507540343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677143294393892676720457 507857470795419507540343)
                ·
                  refine ⟨761786206193129261310515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507857470795419507540343 761786206193129261310515)
                  ·
                    refine ⟨1142679309289693891965773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 761786206193129261310515 1142679309289693891965773)
                    ·
                      refine ⟨428504740983635209487165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1142679309289693891965773 428504740983635209487165)
                      ·
                        rfl

theorem cell23_834510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_834510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834510 prefixEnd_834510 := by exact prefixLift 834510
  have htrace : WordTrace (prefixWord ++ tailWord_834510) baseStart_834510 baseEnd_834510 := by
    simpa [prefixWord, tailWord_834510, baseEnd_834510] using wordTrace_append hprefix tailTrace_834510
  have hstable : (prefixWord ++ tailWord_834510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834510).length < 2 ^ (prefixWord ++ tailWord_834510).sum := by decide
  have hdescent : baseEnd_834510 < baseStart_834510 := by decide
  rcases family_descends (prefixWord ++ tailWord_834510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834522 : List Nat := [3, 1, 1, 2, 4, 1, 3, 8]
def baseStart_834522 : Nat := 118140960795 + 834522 * 2 ^ 59
def prefixEnd_834522 : Nat := 4983230072969 + 3 ^ 40 * 834522 * 2
def baseEnd_834522 : Nat := 15870774175981080093967

theorem tailTrace_834522 : CollatzResearch.WordTrace tailWord_834522 prefixEnd_834522 15870774175981080093967 := by
  unfold tailWord_834522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7609379470669198463928455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20291678588451195903809213 7609379470669198463928455)
  ·
    refine ⟨11414069206003797695892683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7609379470669198463928455 11414069206003797695892683)
    ·
      refine ⟨17121103809005696543839025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11414069206003797695892683 17121103809005696543839025)
      ·
        refine ⟨12840827856754272407879269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17121103809005696543839025 12840827856754272407879269)
        ·
          refine ⟨2407655223141426076477363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12840827856754272407879269 2407655223141426076477363)
          ·
            refine ⟨3611482834712139114716045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407655223141426076477363 3611482834712139114716045)
            ·
              refine ⟨1354306063017052168018517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3611482834712139114716045 1354306063017052168018517)
              ·
                refine ⟨15870774175981080093967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1354306063017052168018517 15870774175981080093967)
                ·
                  rfl

theorem cell23_834522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 8].length) (baseStart_834522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834522 prefixEnd_834522 := by exact prefixLift 834522
  have htrace : WordTrace (prefixWord ++ tailWord_834522) baseStart_834522 baseEnd_834522 := by
    simpa [prefixWord, tailWord_834522, baseEnd_834522] using wordTrace_append hprefix tailTrace_834522
  have hstable : (prefixWord ++ tailWord_834522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834522).length < 2 ^ (prefixWord ++ tailWord_834522).sum := by decide
  have hdescent : baseEnd_834522 < baseStart_834522 := by decide
  rcases family_descends (prefixWord ++ tailWord_834522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834550 : List Nat := [5, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_834550 : Nat := 118140960795 + 834550 * 2 ^ 59
def prefixEnd_834550 : Nat := 4983230072969 + 3 ^ 40 * 834550 * 2
def baseEnd_834550 : Nat := 428525280209815052986981

theorem tailTrace_834550 : CollatzResearch.WordTrace tailWord_834550 prefixEnd_834550 428525280209815052986981 := by
  unfold tailWord_834550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1902408695410959664858319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20292359417716903091822069 1902408695410959664858319)
  ·
    refine ⟨2853613043116439497287479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1902408695410959664858319 2853613043116439497287479)
    ·
      refine ⟨4280419564674659245931219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2853613043116439497287479 4280419564674659245931219)
      ·
        refine ⟨6420629347011988868896829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4280419564674659245931219 6420629347011988868896829)
        ·
          refine ⟨2407736005129495825836311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6420629347011988868896829 2407736005129495825836311)
          ·
            refine ⟨3611604007694243738754467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407736005129495825836311 3611604007694243738754467)
            ·
              refine ⟨5417406011541365608131701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3611604007694243738754467 5417406011541365608131701)
              ·
                refine ⟨507881813582003025762347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5417406011541365608131701 507881813582003025762347)
                ·
                  refine ⟨761822720373004538643521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507881813582003025762347 761822720373004538643521)
                  ·
                    refine ⟨571367040279753403982641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 761822720373004538643521 571367040279753403982641)
                    ·
                      refine ⟨428525280209815052986981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571367040279753403982641 428525280209815052986981)
                      ·
                        rfl

theorem cell23_834550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_834550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834550 prefixEnd_834550 := by exact prefixLift 834550
  have htrace : WordTrace (prefixWord ++ tailWord_834550) baseStart_834550 baseEnd_834550 := by
    simpa [prefixWord, tailWord_834550, baseEnd_834550] using wordTrace_append hprefix tailTrace_834550
  have hstable : (prefixWord ++ tailWord_834550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834550).length < 2 ^ (prefixWord ++ tailWord_834550).sum := by decide
  have hdescent : baseEnd_834550 < baseStart_834550 := by decide
  rcases family_descends (prefixWord ++ tailWord_834550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834593 : List Nat := [1, 2, 3, 2, 3, 2, 2, 2, 1, 3, 2]
def baseStart_834593 : Nat := 118140960795 + 834593 * 2 ^ 59
def prefixEnd_834593 : Nat := 4983230072969 + 3 ^ 40 * 834593 * 2
def baseEnd_834593 : Nat := 428547359877958384749283

theorem tailTrace_834593 : CollatzResearch.WordTrace tailWord_834593 prefixEnd_834593 428547359877958384749283 := by
  unfold tailWord_834593
  simp only [CollatzResearch.WordTrace]
  refine ⟨30440107465419572981548433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20293404976946381987698955 30440107465419572981548433)
  ·
    refine ⟨22830080599064679736161325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30440107465419572981548433 22830080599064679736161325)
    ·
      refine ⟨8561280224649254901060497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22830080599064679736161325 8561280224649254901060497)
      ·
        refine ⟨6420960168486941175795373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8561280224649254901060497 6420960168486941175795373)
        ·
          refine ⟨2407860063182602940923265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6420960168486941175795373 2407860063182602940923265)
          ·
            refine ⟨1805895047386952205692449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2407860063182602940923265 1805895047386952205692449)
            ·
              refine ⟨1354421285540214154269337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1805895047386952205692449 1354421285540214154269337)
              ·
                refine ⟨1015815964155160615702003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354421285540214154269337 1015815964155160615702003)
                ·
                  refine ⟨1523723946232740923553005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015815964155160615702003 1523723946232740923553005)
                  ·
                    refine ⟨571396479837277846332377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1523723946232740923553005 571396479837277846332377)
                    ·
                      refine ⟨428547359877958384749283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571396479837277846332377 428547359877958384749283)
                      ·
                        rfl

theorem cell23_834593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_834593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834593 prefixEnd_834593 := by exact prefixLift 834593
  have htrace : WordTrace (prefixWord ++ tailWord_834593) baseStart_834593 baseEnd_834593 := by
    simpa [prefixWord, tailWord_834593, baseEnd_834593] using wordTrace_append hprefix tailTrace_834593
  have hstable : (prefixWord ++ tailWord_834593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834593).length < 2 ^ (prefixWord ++ tailWord_834593).sum := by decide
  have hdescent : baseEnd_834593 < baseStart_834593 := by decide
  rcases family_descends (prefixWord ++ tailWord_834593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834606 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_834606 : Nat := 118140960795 + 834606 * 2 ^ 59
def prefixEnd_834606 : Nat := 4983230072969 + 3 ^ 40 * 834606 * 2
def baseEnd_834606 : Nat := 428554035126466833886723

theorem tailTrace_834606 : CollatzResearch.WordTrace tailWord_834606 prefixEnd_834606 428554035126466833886723 := by
  unfold tailWord_834606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3805072701796559525221459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20293721076248317467847781 3805072701796559525221459)
  ·
    refine ⟨5707609052694839287832189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3805072701796559525221459 5707609052694839287832189)
    ·
      refine ⟨2140353394760564732937071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5707609052694839287832189 2140353394760564732937071)
      ·
        refine ⟨3210530092140847099405607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140353394760564732937071 3210530092140847099405607)
        ·
          refine ⟨4815795138211270649108411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3210530092140847099405607 4815795138211270649108411)
          ·
            refine ⟨7223692707316905973662617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4815795138211270649108411 7223692707316905973662617)
            ·
              refine ⟨5417769530487679480246963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7223692707316905973662617 5417769530487679480246963)
              ·
                refine ⟨8126654295731519220370445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5417769530487679480246963 8126654295731519220370445)
                ·
                  refine ⟨3047495360899319707638917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8126654295731519220370445 3047495360899319707638917)
                  ·
                    refine ⟨571405380168622445182297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3047495360899319707638917 571405380168622445182297)
                    ·
                      refine ⟨428554035126466833886723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571405380168622445182297 428554035126466833886723)
                      ·
                        rfl

theorem cell23_834606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_834606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834606 prefixEnd_834606 := by exact prefixLift 834606
  have htrace : WordTrace (prefixWord ++ tailWord_834606) baseStart_834606 baseEnd_834606 := by
    simpa [prefixWord, tailWord_834606, baseEnd_834606] using wordTrace_append hprefix tailTrace_834606
  have hstable : (prefixWord ++ tailWord_834606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834606).length < 2 ^ (prefixWord ++ tailWord_834606).sum := by decide
  have hdescent : baseEnd_834606 < baseStart_834606 := by decide
  rcases family_descends (prefixWord ++ tailWord_834606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834629 : List Nat := [1, 3, 1, 1, 1, 3, 2, 6, 5]
def baseStart_834629 : Nat := 118140960795 + 834629 * 2 ^ 59
def prefixEnd_834629 : Nat := 4983230072969 + 3 ^ 40 * 834629 * 2
def baseEnd_834629 : Nat := 47618427242391138211013

theorem tailTrace_834629 : CollatzResearch.WordTrace tailWord_834629 prefixEnd_834629 47618427242391138211013 := by
  unfold tailWord_834629
  simp only [CollatzResearch.WordTrace]
  refine ⟨30441420493289151129858941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20294280328859434086572627 30441420493289151129858941)
  ·
    refine ⟨11415532684983431673697103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30441420493289151129858941 11415532684983431673697103)
    ·
      refine ⟨17123299027475147510545655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11415532684983431673697103 17123299027475147510545655)
      ·
        refine ⟨25684948541212721265818483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17123299027475147510545655 25684948541212721265818483)
        ·
          refine ⟨38527422811819081898727725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25684948541212721265818483 38527422811819081898727725)
          ·
            refine ⟨14447783554432155712022897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38527422811819081898727725 14447783554432155712022897)
            ·
              refine ⟨10835837665824116784017173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14447783554432155712022897 10835837665824116784017173)
              ·
                refine ⟨507929890585505474250805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10835837665824116784017173 507929890585505474250805)
                ·
                  refine ⟨47618427242391138211013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 507929890585505474250805 47618427242391138211013)
                  ·
                    rfl

theorem cell23_834629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 6, 5].length) (baseStart_834629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834629 prefixEnd_834629 := by exact prefixLift 834629
  have htrace : WordTrace (prefixWord ++ tailWord_834629) baseStart_834629 baseEnd_834629 := by
    simpa [prefixWord, tailWord_834629, baseEnd_834629] using wordTrace_append hprefix tailTrace_834629
  have hstable : (prefixWord ++ tailWord_834629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834629).length < 2 ^ (prefixWord ++ tailWord_834629).sum := by decide
  have hdescent : baseEnd_834629 < baseStart_834629 := by decide
  rcases family_descends (prefixWord ++ tailWord_834629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834649 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 4, 5, 2]
def baseStart_834649 : Nat := 118140960795 + 834649 * 2 ^ 59
def prefixEnd_834649 : Nat := 4983230072969 + 3 ^ 40 * 834649 * 2
def baseEnd_834649 : Nat := 428576114794610165649025

theorem tailTrace_834649 : CollatzResearch.WordTrace tailWord_834649 prefixEnd_834649 428576114794610165649025 := by
  unfold tailWord_834649
  simp only [CollatzResearch.WordTrace]
  refine ⟨30442149953216694545587001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20294766635477796363724667 30442149953216694545587001)
  ·
    refine ⟨22831612464912520909190251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30442149953216694545587001 22831612464912520909190251)
    ·
      refine ⟨34247418697368781363785377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22831612464912520909190251 34247418697368781363785377)
      ·
        refine ⟨25685564023026586022839033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34247418697368781363785377 25685564023026586022839033)
        ·
          refine ⟨19264173017269939517129275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25685564023026586022839033 19264173017269939517129275)
          ·
            refine ⟨28896259525904909275693913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19264173017269939517129275 28896259525904909275693913)
            ·
              refine ⟨21672194644428681956770435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28896259525904909275693913 21672194644428681956770435)
              ·
                refine ⟨32508291966643022935155653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21672194644428681956770435 32508291966643022935155653)
                ·
                  refine ⟨6095304743745566800341685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32508291966643022935155653 6095304743745566800341685)
                  ·
                    refine ⟨571434819726146887532033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6095304743745566800341685 571434819726146887532033)
                    ·
                      refine ⟨428576114794610165649025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571434819726146887532033 428576114794610165649025)
                      ·
                        rfl

theorem cell23_834649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 5, 2].length) (baseStart_834649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834649 prefixEnd_834649 := by exact prefixLift 834649
  have htrace : WordTrace (prefixWord ++ tailWord_834649) baseStart_834649 baseEnd_834649 := by
    simpa [prefixWord, tailWord_834649, baseEnd_834649] using wordTrace_append hprefix tailTrace_834649
  have hstable : (prefixWord ++ tailWord_834649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834649).length < 2 ^ (prefixWord ++ tailWord_834649).sum := by decide
  have hdescent : baseEnd_834649 < baseStart_834649 := by decide
  rcases family_descends (prefixWord ++ tailWord_834649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834669 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_834669 : Nat := 118140960795 + 834669 * 2 ^ 59
def prefixEnd_834669 : Nat := 4983230072969 + 3 ^ 40 * 834669 * 2
def baseEnd_834669 : Nat := 428586384407700087398933

theorem tailTrace_834669 : CollatzResearch.WordTrace tailWord_834669 prefixEnd_834669 428586384407700087398933 := by
  unfold tailWord_834669
  simp only [CollatzResearch.WordTrace]
  refine ⟨30442879413144237961315061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20295252942096158640876707 30442879413144237961315061)
  ·
    refine ⟨2854019944982272308873287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30442879413144237961315061 2854019944982272308873287)
    ·
      refine ⟨4281029917473408463309931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2854019944982272308873287 4281029917473408463309931)
      ·
        refine ⟨6421544876210112694964897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4281029917473408463309931 6421544876210112694964897)
        ·
          refine ⟨4816158657157584521223673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6421544876210112694964897 4816158657157584521223673)
          ·
            refine ⟨3612118992868188390917755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4816158657157584521223673 3612118992868188390917755)
            ·
              refine ⟨5418178489302282586376633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3612118992868188390917755 5418178489302282586376633)
              ·
                refine ⟨4063633866976711939782475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5418178489302282586376633 4063633866976711939782475)
                ·
                  refine ⟨6095450800465067909673713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063633866976711939782475 6095450800465067909673713)
                  ·
                    refine ⟨4571588100348800932255285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6095450800465067909673713 4571588100348800932255285)
                    ·
                      refine ⟨428586384407700087398933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4571588100348800932255285 428586384407700087398933)
                      ·
                        rfl

theorem cell23_834669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_834669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834669 prefixEnd_834669 := by exact prefixLift 834669
  have htrace : WordTrace (prefixWord ++ tailWord_834669) baseStart_834669 baseEnd_834669 := by
    simpa [prefixWord, tailWord_834669, baseEnd_834669] using wordTrace_append hprefix tailTrace_834669
  have hstable : (prefixWord ++ tailWord_834669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834669).length < 2 ^ (prefixWord ++ tailWord_834669).sum := by decide
  have hdescent : baseEnd_834669 < baseStart_834669 := by decide
  rcases family_descends (prefixWord ++ tailWord_834669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834679 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_834679 : Nat := 118140960795 + 834679 * 2 ^ 59
def prefixEnd_834679 : Nat := 4983230072969 + 3 ^ 40 * 834679 * 2
def baseEnd_834679 : Nat := 428591519214245048273887

theorem tailTrace_834679 : CollatzResearch.WordTrace tailWord_834679 prefixEnd_834679 428591519214245048273887 := by
  unfold tailWord_834679
  simp only [CollatzResearch.WordTrace]
  refine ⟨30443244143108009669179091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20295496095405339779452727 30443244143108009669179091)
  ·
    refine ⟨45664866214662014503768637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30443244143108009669179091 45664866214662014503768637)
    ·
      refine ⟨17124324830498255438913239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45664866214662014503768637 17124324830498255438913239)
      ·
        refine ⟨25686487245747383158369859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17124324830498255438913239 25686487245747383158369859)
        ·
          refine ⟨38529730868621074737554789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25686487245747383158369859 38529730868621074737554789)
          ·
            refine ⟨7224324537866451513291523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38529730868621074737554789 7224324537866451513291523)
            ·
              refine ⟨10836486806799677269937285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7224324537866451513291523 10836486806799677269937285)
              ·
                refine ⟨2031841276274939488113241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10836486806799677269937285 2031841276274939488113241)
                ·
                  refine ⟨1523880957206204616084931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2031841276274939488113241 1523880957206204616084931)
                  ·
                    refine ⟨2285821435809306924127397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1523880957206204616084931 2285821435809306924127397)
                    ·
                      refine ⟨428591519214245048273887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2285821435809306924127397 428591519214245048273887)
                      ·
                        rfl

theorem cell23_834679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_834679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834679 prefixEnd_834679 := by exact prefixLift 834679
  have htrace : WordTrace (prefixWord ++ tailWord_834679) baseStart_834679 baseEnd_834679 := by
    simpa [prefixWord, tailWord_834679, baseEnd_834679] using wordTrace_append hprefix tailTrace_834679
  have hstable : (prefixWord ++ tailWord_834679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834679).length < 2 ^ (prefixWord ++ tailWord_834679).sum := by decide
  have hdescent : baseEnd_834679 < baseStart_834679 := by decide
  rcases family_descends (prefixWord ++ tailWord_834679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834699 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 3]
def baseStart_834699 : Nat := 118140960795 + 834699 * 2 ^ 59
def prefixEnd_834699 : Nat := 4983230072969 + 3 ^ 40 * 834699 * 2
def baseEnd_834699 : Nat := 428601788827334970023795

theorem tailTrace_834699 : CollatzResearch.WordTrace tailWord_834699 prefixEnd_834699 428601788827334970023795 := by
  unfold tailWord_834699
  simp only [CollatzResearch.WordTrace]
  refine ⟨30443973603035553084907151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20295982402023702056604767 30443973603035553084907151)
  ·
    refine ⟨45665960404553329627360727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30443973603035553084907151 45665960404553329627360727)
    ·
      refine ⟨68498940606829994441041091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45665960404553329627360727 68498940606829994441041091)
      ·
        refine ⟨102748410910244991661561637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68498940606829994441041091 102748410910244991661561637)
        ·
          refine ⟨19265327045670935936542807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102748410910244991661561637 19265327045670935936542807)
          ·
            refine ⟨28897990568506403904814211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19265327045670935936542807 28897990568506403904814211)
            ·
              refine ⟨43346985852759605857221317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28897990568506403904814211 43346985852759605857221317)
              ·
                refine ⟨8127559847392426098228997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43346985852759605857221317 8127559847392426098228997)
                ·
                  refine ⟨1523917471386079893417937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8127559847392426098228997 1523917471386079893417937)
                  ·
                    refine ⟨1142938103539559920063453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1523917471386079893417937 1142938103539559920063453)
                    ·
                      refine ⟨428601788827334970023795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1142938103539559920063453 428601788827334970023795)
                      ·
                        rfl

theorem cell23_834699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 3].length) (baseStart_834699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834699 prefixEnd_834699 := by exact prefixLift 834699
  have htrace : WordTrace (prefixWord ++ tailWord_834699) baseStart_834699 baseEnd_834699 := by
    simpa [prefixWord, tailWord_834699, baseEnd_834699] using wordTrace_append hprefix tailTrace_834699
  have hstable : (prefixWord ++ tailWord_834699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834699).length < 2 ^ (prefixWord ++ tailWord_834699).sum := by decide
  have hdescent : baseEnd_834699 < baseStart_834699 := by decide
  rcases family_descends (prefixWord ++ tailWord_834699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834706 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_834706 : Nat := 118140960795 + 834706 * 2 ^ 59
def prefixEnd_834706 : Nat := 4983230072969 + 3 ^ 40 * 834706 * 2
def baseEnd_834706 : Nat := 142868461063972147545421

theorem tailTrace_834706 : CollatzResearch.WordTrace tailWord_834706 prefixEnd_834706 142868461063972147545421 := by
  unfold tailWord_834706
  simp only [CollatzResearch.WordTrace]
  refine ⟨7611057228502548320102993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20296152609340128853607981 7611057228502548320102993)
  ·
    refine ⟨5708292921376911240077245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7611057228502548320102993 5708292921376911240077245)
    ·
      refine ⟨2140609845516341715028967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5708292921376911240077245 2140609845516341715028967)
      ·
        refine ⟨3210914768274512572543451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140609845516341715028967 3210914768274512572543451)
        ·
          refine ⟨4816372152411768858815177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3210914768274512572543451 4816372152411768858815177)
          ·
            refine ⟨3612279114308826644111383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4816372152411768858815177 3612279114308826644111383)
            ·
              refine ⟨5418418671463239966167075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3612279114308826644111383 5418418671463239966167075)
              ·
                refine ⟨8127628007194859949250613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5418418671463239966167075 8127628007194859949250613)
                ·
                  refine ⟨761965125674518120242245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8127628007194859949250613 761965125674518120242245)
                  ·
                    refine ⟨142868461063972147545421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 761965125674518120242245 142868461063972147545421)
                    ·
                      rfl

theorem cell23_834706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_834706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834706 prefixEnd_834706 := by exact prefixLift 834706
  have htrace : WordTrace (prefixWord ++ tailWord_834706) baseStart_834706 baseEnd_834706 := by
    simpa [prefixWord, tailWord_834706, baseEnd_834706] using wordTrace_append hprefix tailTrace_834706
  have hstable : (prefixWord ++ tailWord_834706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834706).length < 2 ^ (prefixWord ++ tailWord_834706).sum := by decide
  have hdescent : baseEnd_834706 < baseStart_834706 := by decide
  rcases family_descends (prefixWord ++ tailWord_834706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834716 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_834716 : Nat := 118140960795 + 834716 * 2 ^ 59
def prefixEnd_834716 : Nat := 4983230072969 + 3 ^ 40 * 834716 * 2
def baseEnd_834716 : Nat := 428610517998461403511217

theorem tailTrace_834716 : CollatzResearch.WordTrace tailWord_834716 prefixEnd_834716 428610517998461403511217 := by
  unfold tailWord_834716
  simp only [CollatzResearch.WordTrace]
  refine ⟨15222296821986982494138001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20296395762649309992184001 15222296821986982494138001)
  ·
    refine ⟨11416722616490236870603501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15222296821986982494138001 11416722616490236870603501)
    ·
      refine ⟨4281270981183838826476313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11416722616490236870603501 4281270981183838826476313)
      ·
        refine ⟨3210953235887879119857235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4281270981183838826476313 3210953235887879119857235)
        ·
          refine ⟨4816429853831818679785853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3210953235887879119857235 4816429853831818679785853)
          ·
            refine ⟨1806161195186932004919695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4816429853831818679785853 1806161195186932004919695)
            ·
              refine ⟨2709241792780398007379543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806161195186932004919695 2709241792780398007379543)
              ·
                refine ⟨4063862689170597011069315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709241792780398007379543 4063862689170597011069315)
                ·
                  refine ⟨6095794033755895516603973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4063862689170597011069315 6095794033755895516603973)
                  ·
                    refine ⟨1142961381329230409363245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6095794033755895516603973 1142961381329230409363245)
                    ·
                      refine ⟨428610517998461403511217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1142961381329230409363245 428610517998461403511217)
                      ·
                        rfl

theorem cell23_834716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_834716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834716 prefixEnd_834716 := by exact prefixLift 834716
  have htrace : WordTrace (prefixWord ++ tailWord_834716) baseStart_834716 baseEnd_834716 := by
    simpa [prefixWord, tailWord_834716, baseEnd_834716] using wordTrace_append hprefix tailTrace_834716
  have hstable : (prefixWord ++ tailWord_834716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834716).length < 2 ^ (prefixWord ++ tailWord_834716).sum := by decide
  have hdescent : baseEnd_834716 < baseStart_834716 := by decide
  rcases family_descends (prefixWord ++ tailWord_834716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834749 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_834749 : Nat := 118140960795 + 834749 * 2 ^ 59
def prefixEnd_834749 : Nat := 4983230072969 + 3 ^ 40 * 834749 * 2
def baseEnd_834749 : Nat := 142875820953353258132855

theorem tailTrace_834749 : CollatzResearch.WordTrace tailWord_834749 prefixEnd_834749 142875820953353258132855 := by
  unfold tailWord_834749
  simp only [CollatzResearch.WordTrace]
  refine ⟨30445797252854411624227301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20297198168569607749484867 30445797252854411624227301)
  ·
    refine ⟨5708586984910202179542619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30445797252854411624227301 5708586984910202179542619)
    ·
      refine ⟨8562880477365303269313929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5708586984910202179542619 8562880477365303269313929)
      ·
        refine ⟨6422160358023977451985447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8562880477365303269313929 6422160358023977451985447)
        ·
          refine ⟨9633240537035966177978171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6422160358023977451985447 9633240537035966177978171)
          ·
            refine ⟨14449860805553949266967257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9633240537035966177978171 14449860805553949266967257)
            ·
              refine ⟨10837395604165461950225443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14449860805553949266967257 10837395604165461950225443)
              ·
                refine ⟨16256093406248192925338165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10837395604165461950225443 16256093406248192925338165)
                ·
                  refine ⟨1524008756835768086750453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16256093406248192925338165 1524008756835768086750453)
                  ·
                    refine ⟨142875820953353258132855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1524008756835768086750453 142875820953353258132855)
                    ·
                      rfl

theorem cell23_834749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_834749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834749 prefixEnd_834749 := by exact prefixLift 834749
  have htrace : WordTrace (prefixWord ++ tailWord_834749) baseStart_834749 baseEnd_834749 := by
    simpa [prefixWord, tailWord_834749, baseEnd_834749] using wordTrace_append hprefix tailTrace_834749
  have hstable : (prefixWord ++ tailWord_834749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834749).length < 2 ^ (prefixWord ++ tailWord_834749).sum := by decide
  have hdescent : baseEnd_834749 < baseStart_834749 := by decide
  rcases family_descends (prefixWord ++ tailWord_834749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834773 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 1, 5, 2]
def baseStart_834773 : Nat := 118140960795 + 834773 * 2 ^ 59
def prefixEnd_834773 : Nat := 4983230072969 + 3 ^ 40 * 834773 * 2
def baseEnd_834773 : Nat := 428639786395767680498455

theorem tailTrace_834773 : CollatzResearch.WordTrace tailWord_834773 prefixEnd_834773 428639786395767680498455 := by
  unfold tailWord_834773
  simp only [CollatzResearch.WordTrace]
  refine ⟨30446672604767463723100973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20297781736511642482067315 30446672604767463723100973)
  ·
    refine ⟨11417502226787798896162865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30446672604767463723100973 11417502226787798896162865)
    ·
      refine ⟨8563126670090849172122149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11417502226787798896162865 8563126670090849172122149)
      ·
        refine ⟨1605586250642034219772903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8563126670090849172122149 1605586250642034219772903)
        ·
          refine ⟨2408379375963051329659355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605586250642034219772903 2408379375963051329659355)
          ·
            refine ⟨3612569063944576994489033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2408379375963051329659355 3612569063944576994489033)
            ·
              refine ⟨2709426797958432745866775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3612569063944576994489033 2709426797958432745866775)
              ·
                refine ⟨4064140196937649118800163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709426797958432745866775 4064140196937649118800163)
                ·
                  refine ⟨6096210295406473678200245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4064140196937649118800163 6096210295406473678200245)
                  ·
                    refine ⟨571519715194356907331273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6096210295406473678200245 571519715194356907331273)
                    ·
                      refine ⟨428639786395767680498455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571519715194356907331273 428639786395767680498455)
                      ·
                        rfl

theorem cell23_834773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_834773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834773 prefixEnd_834773 := by exact prefixLift 834773
  have htrace : WordTrace (prefixWord ++ tailWord_834773) baseStart_834773 baseEnd_834773 := by
    simpa [prefixWord, tailWord_834773, baseEnd_834773] using wordTrace_append hprefix tailTrace_834773
  have hstable : (prefixWord ++ tailWord_834773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834773).length < 2 ^ (prefixWord ++ tailWord_834773).sum := by decide
  have hdescent : baseEnd_834773 < baseStart_834773 := by decide
  rcases family_descends (prefixWord ++ tailWord_834773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834774 : List Nat := [5, 2, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_834774 : Nat := 118140960795 + 834774 * 2 ^ 59
def prefixEnd_834774 : Nat := 4983230072969 + 3 ^ 40 * 834774 * 2
def baseEnd_834774 : Nat := 142880099958807392195317

theorem tailTrace_834774 : CollatzResearch.WordTrace tailWord_834774 prefixEnd_834774 142880099958807392195317 := by
  unfold tailWord_834774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1902919317360240055867961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20297806051842560595924917 1902919317360240055867961)
  ·
    refine ⟨1427189488020180041900971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1902919317360240055867961 1427189488020180041900971)
    ·
      refine ⟨2140784232030270062851457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1427189488020180041900971 2140784232030270062851457)
      ·
        refine ⟨1605588174022702547138593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2140784232030270062851457 1605588174022702547138593)
        ·
          refine ⟨1204191130517026910353945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1605588174022702547138593 1204191130517026910353945)
          ·
            refine ⟨903143347887770182765459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204191130517026910353945 903143347887770182765459)
            ·
              refine ⟨1354715021831655274148189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903143347887770182765459 1354715021831655274148189)
              ·
                refine ⟨508018133186870727805571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1354715021831655274148189 508018133186870727805571)
                ·
                  refine ⟨762027199780306091708357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508018133186870727805571 762027199780306091708357)
                  ·
                    refine ⟨142880099958807392195317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 762027199780306091708357 142880099958807392195317)
                    ·
                      rfl

theorem cell23_834774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_834774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834774 prefixEnd_834774 := by exact prefixLift 834774
  have htrace : WordTrace (prefixWord ++ tailWord_834774) baseStart_834774 baseEnd_834774 := by
    simpa [prefixWord, tailWord_834774, baseEnd_834774] using wordTrace_append hprefix tailTrace_834774
  have hstable : (prefixWord ++ tailWord_834774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834774).length < 2 ^ (prefixWord ++ tailWord_834774).sum := by decide
  have hdescent : baseEnd_834774 < baseStart_834774 := by decide
  rcases family_descends (prefixWord ++ tailWord_834774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834796 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 4, 4]
def baseStart_834796 : Nat := 118140960795 + 834796 * 2 ^ 59
def prefixEnd_834796 : Nat := 4983230072969 + 3 ^ 40 * 834796 * 2
def baseEnd_834796 : Nat := 142883865483607030170283

theorem tailTrace_834796 : CollatzResearch.WordTrace tailWord_834796 prefixEnd_834796 142883865483607030170283 := by
  unfold tailWord_834796
  simp only [CollatzResearch.WordTrace]
  refine ⟨15223755741842069325594121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20298340989122759100792161 15223755741842069325594121)
  ·
    refine ⟨11417816806381551994195591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15223755741842069325594121 11417816806381551994195591)
    ·
      refine ⟨17126725209572327991293387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11417816806381551994195591 17126725209572327991293387)
      ·
        refine ⟨25690087814358491986940081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17126725209572327991293387 25690087814358491986940081)
        ·
          refine ⟨19267565860768868990205061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25690087814358491986940081 19267565860768868990205061)
          ·
            refine ⟨3612668598894162935663449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19267565860768868990205061 3612668598894162935663449)
            ·
              refine ⟨2709501449170622201747587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3612668598894162935663449 2709501449170622201747587)
              ·
                refine ⟨4064252173755933302621381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709501449170622201747587 4064252173755933302621381)
                ·
                  refine ⟨762047282579237494241509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4064252173755933302621381 762047282579237494241509)
                  ·
                    refine ⟨142883865483607030170283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 762047282579237494241509 142883865483607030170283)
                    ·
                      rfl

theorem cell23_834796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_834796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834796 prefixEnd_834796 := by exact prefixLift 834796
  have htrace : WordTrace (prefixWord ++ tailWord_834796) baseStart_834796 baseEnd_834796 := by
    simpa [prefixWord, tailWord_834796, baseEnd_834796] using wordTrace_append hprefix tailTrace_834796
  have hstable : (prefixWord ++ tailWord_834796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834796).length < 2 ^ (prefixWord ++ tailWord_834796).sum := by decide
  have hdescent : baseEnd_834796 < baseStart_834796 := by decide
  rcases family_descends (prefixWord ++ tailWord_834796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834804 : List Nat := [2, 6, 1, 2, 1, 2, 2, 1, 6]
def baseStart_834804 : Nat := 118140960795 + 834804 * 2 ^ 59
def prefixEnd_834804 : Nat := 4983230072969 + 3 ^ 40 * 834804 * 2
def baseEnd_834804 : Nat := 47628411588450784356757

theorem tailTrace_834804 : CollatzResearch.WordTrace tailWord_834804 prefixEnd_834804 47628411588450784356757 := by
  unfold tailWord_834804
  simp only [CollatzResearch.WordTrace]
  refine ⟨15223901633827578008739733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20298535511770104011652977 15223901633827578008739733)
  ·
    refine ⟨713620389085667719159675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15223901633827578008739733 713620389085667719159675)
    ·
      refine ⟨1070430583628501578739513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 713620389085667719159675 1070430583628501578739513)
      ·
        refine ⟨802822937721376184054635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1070430583628501578739513 802822937721376184054635)
        ·
          refine ⟨1204234406582064276081953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802822937721376184054635 1204234406582064276081953)
          ·
            refine ⟨903175804936548207061465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204234406582064276081953 903175804936548207061465)
            ·
              refine ⟨677381853702411155296099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 903175804936548207061465 677381853702411155296099)
              ·
                refine ⟨1016072780553616732944149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677381853702411155296099 1016072780553616732944149)
                ·
                  refine ⟨47628411588450784356757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1016072780553616732944149 47628411588450784356757)
                  ·
                    rfl

theorem cell23_834804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_834804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834804 prefixEnd_834804 := by exact prefixLift 834804
  have htrace : WordTrace (prefixWord ++ tailWord_834804) baseStart_834804 baseEnd_834804 := by
    simpa [prefixWord, tailWord_834804, baseEnd_834804] using wordTrace_append hprefix tailTrace_834804
  have hstable : (prefixWord ++ tailWord_834804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834804).length < 2 ^ (prefixWord ++ tailWord_834804).sum := by decide
  have hdescent : baseEnd_834804 < baseStart_834804 := by decide
  rcases family_descends (prefixWord ++ tailWord_834804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834806 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_834806 : Nat := 118140960795 + 834806 * 2 ^ 59
def prefixEnd_834806 : Nat := 4983230072969 + 3 ^ 40 * 834806 * 2
def baseEnd_834806 : Nat := 428656731257366051385803

theorem tailTrace_834806 : CollatzResearch.WordTrace tailWord_834806 prefixEnd_834806 428656731257366051385803 := by
  unfold tailWord_834806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1902992263352994397440767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20298584142431940239368181 1902992263352994397440767)
  ·
    refine ⟨2854488395029491596161151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1902992263352994397440767 2854488395029491596161151)
    ·
      refine ⟨4281732592544237394241727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2854488395029491596161151 4281732592544237394241727)
      ·
        refine ⟨6422598888816356091362591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4281732592544237394241727 6422598888816356091362591)
        ·
          refine ⟨9633898333224534137043887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6422598888816356091362591 9633898333224534137043887)
          ·
            refine ⟨14450847499836801205565831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9633898333224534137043887 14450847499836801205565831)
            ·
              refine ⟨21676271249755201808348747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14450847499836801205565831 21676271249755201808348747)
              ·
                refine ⟨32514406874632802712523121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21676271249755201808348747 32514406874632802712523121)
                ·
                  refine ⟨24385805155974602034392341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32514406874632802712523121 24385805155974602034392341)
                  ·
                    refine ⟨1143084616686309470362141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24385805155974602034392341 1143084616686309470362141)
                    ·
                      refine ⟨428656731257366051385803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1143084616686309470362141 428656731257366051385803)
                      ·
                        rfl

theorem cell23_834806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_834806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834806 prefixEnd_834806 := by exact prefixLift 834806
  have htrace : WordTrace (prefixWord ++ tailWord_834806) baseStart_834806 baseEnd_834806 := by
    simpa [prefixWord, tailWord_834806, baseEnd_834806] using wordTrace_append hprefix tailTrace_834806
  have hstable : (prefixWord ++ tailWord_834806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834806).length < 2 ^ (prefixWord ++ tailWord_834806).sum := by decide
  have hdescent : baseEnd_834806 < baseStart_834806 := by decide
  rcases family_descends (prefixWord ++ tailWord_834806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834809 : List Nat := [1, 2, 1, 3, 1, 1, 6, 8]
def baseStart_834809 : Nat := 118140960795 + 834809 * 2 ^ 59
def prefixEnd_834809 : Nat := 4983230072969 + 3 ^ 40 * 834809 * 2
def baseEnd_834809 : Nat := 15876232285160353320307

theorem tailTrace_834809 : CollatzResearch.WordTrace tailWord_834809 prefixEnd_834809 15876232285160353320307 := by
  unfold tailWord_834809
  simp only [CollatzResearch.WordTrace]
  refine ⟨30447985632637041871411481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20298657088424694580940987 30447985632637041871411481)
  ·
    refine ⟨22835989224477781403558611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30447985632637041871411481 22835989224477781403558611)
    ·
      refine ⟨34253983836716672105337917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22835989224477781403558611 34253983836716672105337917)
      ·
        refine ⟨12845243938768752039501719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34253983836716672105337917 12845243938768752039501719)
        ·
          refine ⟨19267865908153128059252579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12845243938768752039501719 19267865908153128059252579)
          ·
            refine ⟨28901798862229692088878869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19267865908153128059252579 28901798862229692088878869)
            ·
              refine ⟨1354771821667016816666197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28901798862229692088878869 1354771821667016816666197)
              ·
                refine ⟨15876232285160353320307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1354771821667016816666197 15876232285160353320307)
                ·
                  rfl

theorem cell23_834809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 8].length) (baseStart_834809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834809 prefixEnd_834809 := by exact prefixLift 834809
  have htrace : WordTrace (prefixWord ++ tailWord_834809) baseStart_834809 baseEnd_834809 := by
    simpa [prefixWord, tailWord_834809, baseEnd_834809] using wordTrace_append hprefix tailTrace_834809
  have hstable : (prefixWord ++ tailWord_834809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834809).length < 2 ^ (prefixWord ++ tailWord_834809).sum := by decide
  have hdescent : baseEnd_834809 < baseStart_834809 := by decide
  rcases family_descends (prefixWord ++ tailWord_834809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834820 : List Nat := [2, 3, 2, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_834820 : Nat := 118140960795 + 834820 * 2 ^ 59
def prefixEnd_834820 : Nat := 4983230072969 + 3 ^ 40 * 834820 * 2
def baseEnd_834820 : Nat := 428663919986528996610739

theorem tailTrace_834820 : CollatzResearch.WordTrace tailWord_834820 prefixEnd_834820 428663919986528996610739 := by
  unfold tailWord_834820
  simp only [CollatzResearch.WordTrace]
  refine ⟨15224193417798595375030957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20298924557064793833374609 15224193417798595375030957)
  ·
    refine ⟨5709072531674473265636609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15224193417798595375030957 5709072531674473265636609)
    ·
      refine ⟨4281804398755854949227457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5709072531674473265636609 4281804398755854949227457)
      ·
        refine ⟨3211353299066891211920593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4281804398755854949227457 3211353299066891211920593)
        ·
          refine ⟨2408514974300168408940445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3211353299066891211920593 2408514974300168408940445)
          ·
            refine ⟨903193115362563153352667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2408514974300168408940445 903193115362563153352667)
            ·
              refine ⟨1354789673043844730029001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903193115362563153352667 1354789673043844730029001)
              ·
                refine ⟨1016092254782883547521751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354789673043844730029001 1016092254782883547521751)
                ·
                  refine ⟨1524138382174325321282627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016092254782883547521751 1524138382174325321282627)
                  ·
                    refine ⟨2286207573261487981923941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1524138382174325321282627 2286207573261487981923941)
                    ·
                      refine ⟨428663919986528996610739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2286207573261487981923941 428663919986528996610739)
                      ·
                        rfl

theorem cell23_834820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_834820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834820 prefixEnd_834820 := by exact prefixLift 834820
  have htrace : WordTrace (prefixWord ++ tailWord_834820) baseStart_834820 baseEnd_834820 := by
    simpa [prefixWord, tailWord_834820, baseEnd_834820] using wordTrace_append hprefix tailTrace_834820
  have hstable : (prefixWord ++ tailWord_834820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834820).length < 2 ^ (prefixWord ++ tailWord_834820).sum := by decide
  have hdescent : baseEnd_834820 < baseStart_834820 := by decide
  rcases family_descends (prefixWord ++ tailWord_834820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834840 : List Nat := [2, 1, 2, 3, 1, 4, 3, 1, 1, 2, 3]
def baseStart_834840 : Nat := 118140960795 + 834840 * 2 ^ 59
def prefixEnd_834840 : Nat := 4983230072969 + 3 ^ 40 * 834840 * 2
def baseEnd_834840 : Nat := 428674189599618918360647

theorem tailTrace_834840 : CollatzResearch.WordTrace tailWord_834840 prefixEnd_834840 428674189599618918360647 := by
  unfold tailWord_834840
  simp only [CollatzResearch.WordTrace]
  refine ⟨15224558147762367082894987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20299410863683156110526649 15224558147762367082894987)
  ·
    refine ⟨22836837221643550624342481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15224558147762367082894987 22836837221643550624342481)
    ·
      refine ⟨17127627916232662968256861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22836837221643550624342481 17127627916232662968256861)
      ·
        refine ⟨6422860468587248613096323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17127627916232662968256861 6422860468587248613096323)
        ·
          refine ⟨9634290702880872919644485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6422860468587248613096323 9634290702880872919644485)
          ·
            refine ⟨1806429506790163672433341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9634290702880872919644485 1806429506790163672433341)
            ·
              refine ⟨677411065046311377162503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1806429506790163672433341 677411065046311377162503)
              ·
                refine ⟨1016116597569467065743755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677411065046311377162503 1016116597569467065743755)
                ·
                  refine ⟨1524174896354200598615633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016116597569467065743755 1524174896354200598615633)
                  ·
                    refine ⟨1143131172265650448961725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1524174896354200598615633 1143131172265650448961725)
                    ·
                      refine ⟨428674189599618918360647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1143131172265650448961725 428674189599618918360647)
                      ·
                        rfl

theorem cell23_834840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_834840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834840 prefixEnd_834840 := by exact prefixLift 834840
  have htrace : WordTrace (prefixWord ++ tailWord_834840) baseStart_834840 baseEnd_834840 := by
    simpa [prefixWord, tailWord_834840, baseEnd_834840] using wordTrace_append hprefix tailTrace_834840
  have hstable : (prefixWord ++ tailWord_834840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834840).length < 2 ^ (prefixWord ++ tailWord_834840).sum := by decide
  have hdescent : baseEnd_834840 < baseStart_834840 := by decide
  rcases family_descends (prefixWord ++ tailWord_834840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834856 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 2, 7]
def baseStart_834856 : Nat := 118140960795 + 834856 * 2 ^ 59
def prefixEnd_834856 : Nat := 4983230072969 + 3 ^ 40 * 834856 * 2
def baseEnd_834856 : Nat := 142894135096696951920191

theorem tailTrace_834856 : CollatzResearch.WordTrace tailWord_834856 prefixEnd_834856 142894135096696951920191 := by
  unfold tailWord_834856
  simp only [CollatzResearch.WordTrace]
  refine ⟨15224849931733384449186211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20299799908977845932248281 15224849931733384449186211)
  ·
    refine ⟨22837274897600076673779317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15224849931733384449186211 22837274897600076673779317)
    ·
      refine ⟨2140994521650007188166811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22837274897600076673779317 2140994521650007188166811)
      ·
        refine ⟨3211491782475010782250217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140994521650007188166811 3211491782475010782250217)
        ·
          refine ⟨2408618836856258086687663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3211491782475010782250217 2408618836856258086687663)
          ·
            refine ⟨3612928255284387130031495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2408618836856258086687663 3612928255284387130031495)
            ·
              refine ⟨5419392382926580695047243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3612928255284387130031495 5419392382926580695047243)
              ·
                refine ⟨8129088574389871042570865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5419392382926580695047243 8129088574389871042570865)
                ·
                  refine ⟨6096816430792403281928149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8129088574389871042570865 6096816430792403281928149)
                  ·
                    refine ⟨142894135096696951920191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6096816430792403281928149 142894135096696951920191)
                    ·
                      rfl

theorem cell23_834856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_834856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834856 prefixEnd_834856 := by exact prefixLift 834856
  have htrace : WordTrace (prefixWord ++ tailWord_834856) baseStart_834856 baseEnd_834856 := by
    simpa [prefixWord, tailWord_834856, baseEnd_834856] using wordTrace_append hprefix tailTrace_834856
  have hstable : (prefixWord ++ tailWord_834856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834856).length < 2 ^ (prefixWord ++ tailWord_834856).sum := by decide
  have hdescent : baseEnd_834856 < baseStart_834856 := by decide
  rcases family_descends (prefixWord ++ tailWord_834856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834899 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 9]
def baseStart_834899 : Nat := 118140960795 + 834899 * 2 ^ 59
def prefixEnd_834899 : Nat := 4983230072969 + 3 ^ 40 * 834899 * 2
def baseEnd_834899 : Nat := 47633831662026020835875

theorem tailTrace_834899 : CollatzResearch.WordTrace tailWord_834899 prefixEnd_834899 47633831662026020835875 := by
  unfold tailWord_834899
  simp only [CollatzResearch.WordTrace]
  refine ⟨30451268202310987242187751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20300845468207324828125167 30451268202310987242187751)
  ·
    refine ⟨45676902303466480863281627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30451268202310987242187751 45676902303466480863281627)
    ·
      refine ⟨68515353455199721294922441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45676902303466480863281627 68515353455199721294922441)
      ·
        refine ⟨51386515091399790971191831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68515353455199721294922441 51386515091399790971191831)
        ·
          refine ⟨77079772637099686456787747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51386515091399790971191831 77079772637099686456787747)
          ·
            refine ⟨115619658955649529685181621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77079772637099686456787747 115619658955649529685181621)
            ·
              refine ⟨10839343027092143407985777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115619658955649529685181621 10839343027092143407985777)
              ·
                refine ⟨8129507270319107555989333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10839343027092143407985777 8129507270319107555989333)
                ·
                  refine ⟨47633831662026020835875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8129507270319107555989333 47633831662026020835875)
                  ·
                    rfl

theorem cell23_834899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 9].length) (baseStart_834899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834899 prefixEnd_834899 := by exact prefixLift 834899
  have htrace : WordTrace (prefixWord ++ tailWord_834899) baseStart_834899 baseEnd_834899 := by
    simpa [prefixWord, tailWord_834899, baseEnd_834899] using wordTrace_append hprefix tailTrace_834899
  have hstable : (prefixWord ++ tailWord_834899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834899).length < 2 ^ (prefixWord ++ tailWord_834899).sum := by decide
  have hdescent : baseEnd_834899 < baseStart_834899 := by decide
  rcases family_descends (prefixWord ++ tailWord_834899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834906 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_834906 : Nat := 118140960795 + 834906 * 2 ^ 59
def prefixEnd_834906 : Nat := 4983230072969 + 3 ^ 40 * 834906 * 2
def baseEnd_834906 : Nat := 428708079322815660135343

theorem tailTrace_834906 : CollatzResearch.WordTrace tailWord_834906 prefixEnd_834906 428708079322815660135343 := by
  unfold tailWord_834906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7612880878321406859423143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20301015675523751625128381 7612880878321406859423143)
  ·
    refine ⟨11419321317482110289134715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7612880878321406859423143 11419321317482110289134715)
    ·
      refine ⟨17128981976223165433702073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11419321317482110289134715 17128981976223165433702073)
      ·
        refine ⟨12846736482167374075276555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17128981976223165433702073 12846736482167374075276555)
        ·
          refine ⟨19270104723251061112914833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12846736482167374075276555 19270104723251061112914833)
          ·
            refine ⟨14452578542438295834686125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19270104723251061112914833 14452578542438295834686125)
            ·
              refine ⟨5419716953414360938007297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14452578542438295834686125 5419716953414360938007297)
              ·
                refine ⟨4064787715060770703505473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419716953414360938007297 4064787715060770703505473)
                ·
                  refine ⟨3048590786295578027629105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4064787715060770703505473 3048590786295578027629105)
                  ·
                    refine ⟨2286443089721683520721829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3048590786295578027629105 2286443089721683520721829)
                    ·
                      refine ⟨428708079322815660135343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2286443089721683520721829 428708079322815660135343)
                      ·
                        rfl

theorem cell23_834906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_834906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834906 prefixEnd_834906 := by exact prefixLift 834906
  have htrace : WordTrace (prefixWord ++ tailWord_834906) baseStart_834906 baseEnd_834906 := by
    simpa [prefixWord, tailWord_834906, baseEnd_834906] using wordTrace_append hprefix tailTrace_834906
  have hstable : (prefixWord ++ tailWord_834906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834906).length < 2 ^ (prefixWord ++ tailWord_834906).sum := by decide
  have hdescent : baseEnd_834906 < baseStart_834906 := by decide
  rcases family_descends (prefixWord ++ tailWord_834906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834916 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 7]
def baseStart_834916 : Nat := 118140960795 + 834916 * 2 ^ 59
def prefixEnd_834916 : Nat := 4983230072969 + 3 ^ 40 * 834916 * 2
def baseEnd_834916 : Nat := 47634801569928957890033

theorem tailTrace_834916 : CollatzResearch.WordTrace tailWord_834916 prefixEnd_834916 47634801569928957890033 := by
  unfold tailWord_834916
  simp only [CollatzResearch.WordTrace]
  refine ⟨15225944121624699572778301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20301258828832932763704401 15225944121624699572778301)
  ·
    refine ⟨5709729045609262339791863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15225944121624699572778301 5709729045609262339791863)
    ·
      refine ⟨8564593568413893509687795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5709729045609262339791863 8564593568413893509687795)
      ·
        refine ⟨12846890352620840264531693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8564593568413893509687795 12846890352620840264531693)
        ·
          refine ⟨4817583882232815099199385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12846890352620840264531693 4817583882232815099199385)
          ·
            refine ⟨3613187911674611324399539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4817583882232815099199385 3613187911674611324399539)
            ·
              refine ⟨5419781867511916986599309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3613187911674611324399539 5419781867511916986599309)
              ·
                refine ⟨2032418200316968869974741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5419781867511916986599309 2032418200316968869974741)
                ·
                  refine ⟨47634801569928957890033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2032418200316968869974741 47634801569928957890033)
                  ·
                    rfl

theorem cell23_834916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_834916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834916 prefixEnd_834916 := by exact prefixLift 834916
  have htrace : WordTrace (prefixWord ++ tailWord_834916) baseStart_834916 baseEnd_834916 := by
    simpa [prefixWord, tailWord_834916, baseEnd_834916] using wordTrace_append hprefix tailTrace_834916
  have hstable : (prefixWord ++ tailWord_834916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834916).length < 2 ^ (prefixWord ++ tailWord_834916).sum := by decide
  have hdescent : baseEnd_834916 < baseStart_834916 := by decide
  rcases family_descends (prefixWord ++ tailWord_834916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834927 : List Nat := [1, 1, 2, 1, 3, 1, 7, 1, 2, 2, 2]
def baseStart_834927 : Nat := 118140960795 + 834927 * 2 ^ 59
def prefixEnd_834927 : Nat := 4983230072969 + 3 ^ 40 * 834927 * 2
def baseEnd_834927 : Nat := 428718862416560077972747

theorem tailTrace_834927 : CollatzResearch.WordTrace tailWord_834927 prefixEnd_834927 428718862416560077972747 := by
  unfold tailWord_834927
  simp only [CollatzResearch.WordTrace]
  refine ⟨30452289446209548024207035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20301526297473032016138023 30452289446209548024207035)
  ·
    refine ⟨45678434169314322036310553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30452289446209548024207035 45678434169314322036310553)
    ·
      refine ⟨34258825626985741527232915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45678434169314322036310553 34258825626985741527232915)
      ·
        refine ⟨51388238440478612290849373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34258825626985741527232915 51388238440478612290849373)
        ·
          refine ⟨19270589415179479609068515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51388238440478612290849373 19270589415179479609068515)
          ·
            refine ⟨28905884122769219413602773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19270589415179479609068515 28905884122769219413602773)
            ·
              refine ⟨677481659127403580006315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 28905884122769219413602773 677481659127403580006315)
              ·
                refine ⟨1016222488691105370009473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677481659127403580006315 1016222488691105370009473)
                ·
                  refine ⟨762166866518329027507105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1016222488691105370009473 762166866518329027507105)
                  ·
                    refine ⟨571625149888746770630329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 762166866518329027507105 571625149888746770630329)
                    ·
                      refine ⟨428718862416560077972747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571625149888746770630329 428718862416560077972747)
                      ·
                        rfl

theorem cell23_834927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 2, 2, 2].length) (baseStart_834927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834927 prefixEnd_834927 := by exact prefixLift 834927
  have htrace : WordTrace (prefixWord ++ tailWord_834927) baseStart_834927 baseEnd_834927 := by
    simpa [prefixWord, tailWord_834927, baseEnd_834927] using wordTrace_append hprefix tailTrace_834927
  have hstable : (prefixWord ++ tailWord_834927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834927).length < 2 ^ (prefixWord ++ tailWord_834927).sum := by decide
  have hdescent : baseEnd_834927 < baseStart_834927 := by decide
  rcases family_descends (prefixWord ++ tailWord_834927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834956 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_834956 : Nat := 118140960795 + 834956 * 2 ^ 59
def prefixEnd_834956 : Nat := 4983230072969 + 3 ^ 40 * 834956 * 2
def baseEnd_834956 : Nat := 428733753355540464510113

theorem tailTrace_834956 : CollatzResearch.WordTrace tailWord_834956 prefixEnd_834956 428733753355540464510113 := by
  unfold tailWord_834956
  simp only [CollatzResearch.WordTrace]
  refine ⟨15226673581552242988506361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20302231442069657318008481 15226673581552242988506361)
  ·
    refine ⟨11420005186164182241379771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15226673581552242988506361 11420005186164182241379771)
    ·
      refine ⟨17130007779246273362069657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11420005186164182241379771 17130007779246273362069657)
      ·
        refine ⟨12847505834434705021552243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17130007779246273362069657 12847505834434705021552243)
        ·
          refine ⟨19271258751652057532328365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12847505834434705021552243 19271258751652057532328365)
          ·
            refine ⟨7226722031869521574623137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19271258751652057532328365 7226722031869521574623137)
            ·
              refine ⟨5420041523902141180967353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7226722031869521574623137 5420041523902141180967353)
              ·
                refine ⟨4065031142926605885725515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5420041523902141180967353 4065031142926605885725515)
                ·
                  refine ⟨6097546714389908828588273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4065031142926605885725515 6097546714389908828588273)
                  ·
                    refine ⟨4573160035792431621441205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6097546714389908828588273 4573160035792431621441205)
                    ·
                      refine ⟨428733753355540464510113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4573160035792431621441205 428733753355540464510113)
                      ·
                        rfl

theorem cell23_834956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_834956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834956 prefixEnd_834956 := by exact prefixLift 834956
  have htrace : WordTrace (prefixWord ++ tailWord_834956) baseStart_834956 baseEnd_834956 := by
    simpa [prefixWord, tailWord_834956, baseEnd_834956] using wordTrace_append hprefix tailTrace_834956
  have hstable : (prefixWord ++ tailWord_834956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834956).length < 2 ^ (prefixWord ++ tailWord_834956).sum := by decide
  have hdescent : baseEnd_834956 < baseStart_834956 := by decide
  rcases family_descends (prefixWord ++ tailWord_834956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834973 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_834973 : Nat := 118140960795 + 834973 * 2 ^ 59
def prefixEnd_834973 : Nat := 4983230072969 + 3 ^ 40 * 834973 * 2
def baseEnd_834973 : Nat := 428742482526666897997535

theorem tailTrace_834973 : CollatzResearch.WordTrace tailWord_834973 prefixEnd_834973 428742482526666897997535 := by
  unfold tailWord_834973
  simp only [CollatzResearch.WordTrace]
  refine ⟨30453967204042897880381573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20302644802695265253587715 30453967204042897880381573)
  ·
    refine ⟨5710118850758043352571545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30453967204042897880381573 5710118850758043352571545)
    ·
      refine ⟨4282589138068532514428659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5710118850758043352571545 4282589138068532514428659)
      ·
        refine ⟨6423883707102798771642989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4282589138068532514428659 6423883707102798771642989)
        ·
          refine ⟨2408956390163549539366121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6423883707102798771642989 2408956390163549539366121)
          ·
            refine ⟨1806717292622662154524591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2408956390163549539366121 1806717292622662154524591)
            ·
              refine ⟨2710075938933993231786887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806717292622662154524591 2710075938933993231786887)
              ·
                refine ⟨4065113908400989847680331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710075938933993231786887 4065113908400989847680331)
                ·
                  refine ⟨6097670862601484771520497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4065113908400989847680331 6097670862601484771520497)
                  ·
                    refine ⟨4573253146951113578640373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6097670862601484771520497 4573253146951113578640373)
                    ·
                      refine ⟨428742482526666897997535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4573253146951113578640373 428742482526666897997535)
                      ·
                        rfl

theorem cell23_834973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_834973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834973 prefixEnd_834973 := by exact prefixLift 834973
  have htrace : WordTrace (prefixWord ++ tailWord_834973) baseStart_834973 baseEnd_834973 := by
    simpa [prefixWord, tailWord_834973, baseEnd_834973] using wordTrace_append hprefix tailTrace_834973
  have hstable : (prefixWord ++ tailWord_834973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834973).length < 2 ^ (prefixWord ++ tailWord_834973).sum := by decide
  have hdescent : baseEnd_834973 < baseStart_834973 := by decide
  rcases family_descends (prefixWord ++ tailWord_834973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834983 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_834983 : Nat := 118140960795 + 834983 * 2 ^ 59
def prefixEnd_834983 : Nat := 4983230072969 + 3 ^ 40 * 834983 * 2
def baseEnd_834983 : Nat := 428747617333211858872489

theorem tailTrace_834983 : CollatzResearch.WordTrace tailWord_834983 prefixEnd_834983 428747617333211858872489 := by
  unfold tailWord_834983
  simp only [CollatzResearch.WordTrace]
  refine ⟨30454331934006669588245603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20302887956004446392163735 30454331934006669588245603)
  ·
    refine ⟨45681497901010004382368405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30454331934006669588245603 45681497901010004382368405)
    ·
      refine ⟨2141320214109843955423519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45681497901010004382368405 2141320214109843955423519)
      ·
        refine ⟨3211980321164765933135279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2141320214109843955423519 3211980321164765933135279)
        ·
          refine ⟨4817970481747148899702919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3211980321164765933135279 4817970481747148899702919)
          ·
            refine ⟨7226955722620723349554379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4817970481747148899702919 7226955722620723349554379)
            ·
              refine ⟨10840433583931085024331569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7226955722620723349554379 10840433583931085024331569)
              ·
                refine ⟨8130325187948313768248677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10840433583931085024331569 8130325187948313768248677)
                ·
                  refine ⟨1524435972740308831546627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8130325187948313768248677 1524435972740308831546627)
                  ·
                    refine ⟨2286653959110463247319941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1524435972740308831546627 2286653959110463247319941)
                    ·
                      refine ⟨428747617333211858872489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2286653959110463247319941 428747617333211858872489)
                      ·
                        rfl

theorem cell23_834983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_834983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834983 prefixEnd_834983 := by exact prefixLift 834983
  have htrace : WordTrace (prefixWord ++ tailWord_834983) baseStart_834983 baseEnd_834983 := by
    simpa [prefixWord, tailWord_834983, baseEnd_834983] using wordTrace_append hprefix tailTrace_834983
  have hstable : (prefixWord ++ tailWord_834983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834983).length < 2 ^ (prefixWord ++ tailWord_834983).sum := by decide
  have hdescent : baseEnd_834983 < baseStart_834983 := by decide
  rcases family_descends (prefixWord ++ tailWord_834983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834993 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 5, 4]
def baseStart_834993 : Nat := 118140960795 + 834993 * 2 ^ 59
def prefixEnd_834993 : Nat := 4983230072969 + 3 ^ 40 * 834993 * 2
def baseEnd_834993 : Nat := 142917584046585606582481

theorem tailTrace_834993 : CollatzResearch.WordTrace tailWord_834993 prefixEnd_834993 142917584046585606582481 := by
  unfold tailWord_834993
  simp only [CollatzResearch.WordTrace]
  refine ⟨30454696663970441296109633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20303131109313627530739755 30454696663970441296109633)
  ·
    refine ⟨22841022497977830972082225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30454696663970441296109633 22841022497977830972082225)
    ·
      refine ⟨17130766873483373229061669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22841022497977830972082225 17130766873483373229061669)
      ·
        refine ⟨3212018788778132480449063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17130766873483373229061669 3212018788778132480449063)
        ·
          refine ⟨4818028183167198720673595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3212018788778132480449063 4818028183167198720673595)
          ·
            refine ⟨7227042274750798081010393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4818028183167198720673595 7227042274750798081010393)
            ·
              refine ⟨5420281706063098560757795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7227042274750798081010393 5420281706063098560757795)
              ·
                refine ⟨8130422559094647841136693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5420281706063098560757795 8130422559094647841136693)
                ·
                  refine ⟨762227114915123235106565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8130422559094647841136693 762227114915123235106565)
                  ·
                    refine ⟨142917584046585606582481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 762227114915123235106565 142917584046585606582481)
                    ·
                      rfl

theorem cell23_834993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_834993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_834993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_834993 prefixEnd_834993 := by exact prefixLift 834993
  have htrace : WordTrace (prefixWord ++ tailWord_834993) baseStart_834993 baseEnd_834993 := by
    simpa [prefixWord, tailWord_834993, baseEnd_834993] using wordTrace_append hprefix tailTrace_834993
  have hstable : (prefixWord ++ tailWord_834993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834993).length < 2 ^ (prefixWord ++ tailWord_834993).sum := by decide
  have hdescent : baseEnd_834993 < baseStart_834993 := by decide
  rcases family_descends (prefixWord ++ tailWord_834993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835020 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 2, 2, 3]
def baseStart_835020 : Nat := 118140960795 + 835020 * 2 ^ 59
def prefixEnd_835020 : Nat := 4983230072969 + 3 ^ 40 * 835020 * 2
def baseEnd_835020 : Nat := 428766616117428214109819

theorem tailTrace_835020 : CollatzResearch.WordTrace tailWord_835020 prefixEnd_835020 428766616117428214109819 := by
  unfold tailWord_835020
  simp only [CollatzResearch.WordTrace]
  refine ⟨15227840717436312453671257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20303787623248416604895009 15227840717436312453671257)
  ·
    refine ⟨11420880538077234340253443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15227840717436312453671257 11420880538077234340253443)
    ·
      refine ⟨17131320807115851510380165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11420880538077234340253443 17131320807115851510380165)
      ·
        refine ⟨3212122651334222158196281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17131320807115851510380165 3212122651334222158196281)
        ·
          refine ⟨2409091988500666618647211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3212122651334222158196281 2409091988500666618647211)
          ·
            refine ⟨3613637982750999927970817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409091988500666618647211 3613637982750999927970817)
            ·
              refine ⟨2710228487063249945978113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3613637982750999927970817 2710228487063249945978113)
              ·
                refine ⟨2032671365297437459483585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2710228487063249945978113 2032671365297437459483585)
                ·
                  refine ⟨1524503523973078094612689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2032671365297437459483585 1524503523973078094612689)
                  ·
                    refine ⟨1143377642979808570959517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1524503523973078094612689 1143377642979808570959517)
                    ·
                      refine ⟨428766616117428214109819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1143377642979808570959517 428766616117428214109819)
                      ·
                        rfl

theorem cell23_835020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_835020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835020 prefixEnd_835020 := by exact prefixLift 835020
  have htrace : WordTrace (prefixWord ++ tailWord_835020) baseStart_835020 baseEnd_835020 := by
    simpa [prefixWord, tailWord_835020, baseEnd_835020] using wordTrace_append hprefix tailTrace_835020
  have hstable : (prefixWord ++ tailWord_835020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835020).length < 2 ^ (prefixWord ++ tailWord_835020).sum := by decide
  have hdescent : baseEnd_835020 < baseStart_835020 := by decide
  rcases family_descends (prefixWord ++ tailWord_835020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835093 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_835093 : Nat := 118140960795 + 835093 * 2 ^ 59
def prefixEnd_835093 : Nat := 4983230072969 + 3 ^ 40 * 835093 * 2
def baseEnd_835093 : Nat := 428804100205206428496983

theorem tailTrace_835093 : CollatzResearch.WordTrace tailWord_835093 prefixEnd_835093 428804100205206428496983 := by
  unfold tailWord_835093
  simp only [CollatzResearch.WordTrace]
  refine ⟨30458343963608158374749933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20305562642405438916499955 30458343963608158374749933)
  ·
    refine ⟨11421878986353059390531225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30458343963608158374749933 11421878986353059390531225)
    ·
      refine ⟨8566409239764794542898419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11421878986353059390531225 8566409239764794542898419)
      ·
        refine ⟨12849613859647191814347629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8566409239764794542898419 12849613859647191814347629)
        ·
          refine ⟨4818605197367696930380361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12849613859647191814347629 4818605197367696930380361)
          ·
            refine ⟨3613953898025772697785271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4818605197367696930380361 3613953898025772697785271)
            ·
              refine ⟨5420930847038659046677907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3613953898025772697785271 5420930847038659046677907)
              ·
                refine ⟨8131396270557988570016861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5420930847038659046677907 8131396270557988570016861)
                ·
                  refine ⟨3049273601459245713756323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8131396270557988570016861 3049273601459245713756323)
                  ·
                    refine ⟨4573910402188868570634485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3049273601459245713756323 4573910402188868570634485)
                    ·
                      refine ⟨428804100205206428496983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4573910402188868570634485 428804100205206428496983)
                      ·
                        rfl

theorem cell23_835093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_835093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835093 prefixEnd_835093 := by exact prefixLift 835093
  have htrace : WordTrace (prefixWord ++ tailWord_835093) baseStart_835093 baseEnd_835093 := by
    simpa [prefixWord, tailWord_835093, baseEnd_835093] using wordTrace_append hprefix tailTrace_835093
  have hstable : (prefixWord ++ tailWord_835093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835093).length < 2 ^ (prefixWord ++ tailWord_835093).sum := by decide
  have hdescent : baseEnd_835093 < baseStart_835093 := by decide
  rcases family_descends (prefixWord ++ tailWord_835093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835107 : List Nat := [1, 1, 1, 4, 5, 1, 2, 2, 1, 1, 4]
def baseStart_835107 : Nat := 118140960795 + 835107 * 2 ^ 59
def prefixEnd_835107 : Nat := 4983230072969 + 3 ^ 40 * 835107 * 2
def baseEnd_835107 : Nat := 428811288934369373721919

theorem tailTrace_835107 : CollatzResearch.WordTrace tailWord_835107 prefixEnd_835107 428811288934369373721919 := by
  unfold tailWord_835107
  simp only [CollatzResearch.WordTrace]
  refine ⟨30458854585557438765759575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20305903057038292510506383 30458854585557438765759575)
  ·
    refine ⟨45688281878336158148639363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30458854585557438765759575 45688281878336158148639363)
    ·
      refine ⟨68532422817504237222959045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45688281878336158148639363 68532422817504237222959045)
      ·
        refine ⟨12849829278282044479304821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68532422817504237222959045 12849829278282044479304821)
        ·
          refine ⟨1204671494838941669934827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12849829278282044479304821 1204671494838941669934827)
          ·
            refine ⟨1807007242258412504902241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204671494838941669934827 1807007242258412504902241)
            ·
              refine ⟨1355255431693809378676681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807007242258412504902241 1355255431693809378676681)
              ·
                refine ⟨1016441573770357034007511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355255431693809378676681 1016441573770357034007511)
                ·
                  refine ⟨1524662360655535551011267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016441573770357034007511 1524662360655535551011267)
                  ·
                    refine ⟨2286993540983303326516901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1524662360655535551011267 2286993540983303326516901)
                    ·
                      refine ⟨428811288934369373721919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2286993540983303326516901 428811288934369373721919)
                      ·
                        rfl

theorem cell23_835107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_835107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835107 prefixEnd_835107 := by exact prefixLift 835107
  have htrace : WordTrace (prefixWord ++ tailWord_835107) baseStart_835107 baseEnd_835107 := by
    simpa [prefixWord, tailWord_835107, baseEnd_835107] using wordTrace_append hprefix tailTrace_835107
  have hstable : (prefixWord ++ tailWord_835107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835107).length < 2 ^ (prefixWord ++ tailWord_835107).sum := by decide
  have hdescent : baseEnd_835107 < baseStart_835107 := by decide
  rcases family_descends (prefixWord ++ tailWord_835107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835141 : List Nat := [1, 3, 1, 1, 1, 4, 5, 2, 1, 2, 2]
def baseStart_835141 : Nat := 118140960795 + 835141 * 2 ^ 59
def prefixEnd_835141 : Nat := 4983230072969 + 3 ^ 40 * 835141 * 2
def baseEnd_835141 : Nat := 428828747276622240696763

theorem tailTrace_835141 : CollatzResearch.WordTrace tailWord_835141 prefixEnd_835141 428828747276622240696763 := by
  unfold tailWord_835141
  simp only [CollatzResearch.WordTrace]
  refine ⟨30460094667434262572497277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20306729778289508381664851 30460094667434262572497277)
  ·
    refine ⟨11422535500287848464686479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30460094667434262572497277 11422535500287848464686479)
    ·
      refine ⟨17133803250431772697029719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11422535500287848464686479 17133803250431772697029719)
      ·
        refine ⟨25700704875647659045544579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17133803250431772697029719 25700704875647659045544579)
        ·
          refine ⟨38551057313471488568316869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25700704875647659045544579 38551057313471488568316869)
          ·
            refine ⟨7228323246275904106559413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38551057313471488568316869 7228323246275904106559413)
            ·
              refine ⟨677655304338366009989945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7228323246275904106559413 677655304338366009989945)
              ·
                refine ⟨508241478253774507492459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677655304338366009989945 508241478253774507492459)
                ·
                  refine ⟨762362217380661761238689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508241478253774507492459 762362217380661761238689)
                  ·
                    refine ⟨571771663035496320929017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 762362217380661761238689 571771663035496320929017)
                    ·
                      refine ⟨428828747276622240696763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571771663035496320929017 428828747276622240696763)
                      ·
                        rfl

theorem cell23_835141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 1, 2, 2].length) (baseStart_835141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835141 prefixEnd_835141 := by exact prefixLift 835141
  have htrace : WordTrace (prefixWord ++ tailWord_835141) baseStart_835141 baseEnd_835141 := by
    simpa [prefixWord, tailWord_835141, baseEnd_835141] using wordTrace_append hprefix tailTrace_835141
  have hstable : (prefixWord ++ tailWord_835141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835141).length < 2 ^ (prefixWord ++ tailWord_835141).sum := by decide
  have hdescent : baseEnd_835141 < baseStart_835141 := by decide
  rcases family_descends (prefixWord ++ tailWord_835141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835150 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2]
def baseStart_835150 : Nat := 118140960795 + 835150 * 2 ^ 59
def prefixEnd_835150 : Nat := 4983230072969 + 3 ^ 40 * 835150 * 2
def baseEnd_835150 : Nat := 428833368602512705484221

theorem tailTrace_835150 : CollatzResearch.WordTrace tailWord_835150 prefixEnd_835150 428833368602512705484221 := by
  unfold tailWord_835150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3807552865550207138696863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20306948616267771406383269 3807552865550207138696863)
  ·
    refine ⟨5711329298325310708045295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3807552865550207138696863 5711329298325310708045295)
    ·
      refine ⟨8566993947487966062067943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5711329298325310708045295 8566993947487966062067943)
      ·
        refine ⟨12850490921231949093101915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8566993947487966062067943 12850490921231949093101915)
        ·
          refine ⟨19275736381847923639652873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12850490921231949093101915 19275736381847923639652873)
          ·
            refine ⟨14456802286385942729739655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19275736381847923639652873 14456802286385942729739655)
            ·
              refine ⟨21685203429578914094609483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14456802286385942729739655 21685203429578914094609483)
              ·
                refine ⟨32527805144368371141914225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21685203429578914094609483 32527805144368371141914225)
                ·
                  refine ⟨24395853858276278356435669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32527805144368371141914225 24395853858276278356435669)
                  ·
                    refine ⟨571777824803350273978961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24395853858276278356435669 571777824803350273978961)
                    ·
                      refine ⟨428833368602512705484221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571777824803350273978961 428833368602512705484221)
                      ·
                        rfl

theorem cell23_835150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_835150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835150 prefixEnd_835150 := by exact prefixLift 835150
  have htrace : WordTrace (prefixWord ++ tailWord_835150) baseStart_835150 baseEnd_835150 := by
    simpa [prefixWord, tailWord_835150, baseEnd_835150] using wordTrace_append hprefix tailTrace_835150
  have hstable : (prefixWord ++ tailWord_835150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835150).length < 2 ^ (prefixWord ++ tailWord_835150).sum := by decide
  have hdescent : baseEnd_835150 < baseStart_835150 := by decide
  rcases family_descends (prefixWord ++ tailWord_835150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835158 : List Nat := [5, 2, 2, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_835158 : Nat := 118140960795 + 835158 * 2 ^ 59
def prefixEnd_835158 : Nat := 4983230072969 + 3 ^ 40 * 835158 * 2
def baseEnd_835158 : Nat := 428837476447748674184185

theorem tailTrace_835158 : CollatzResearch.WordTrace tailWord_835158 prefixEnd_835158 428837476447748674184185 := by
  unfold tailWord_835158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903794669273292154741633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20307143138915116317244085 1903794669273292154741633)
  ·
    refine ⟨1427846001954969116056225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1903794669273292154741633 1427846001954969116056225)
    ·
      refine ⟨1070884501466226837042169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1427846001954969116056225 1070884501466226837042169)
      ·
        refine ⟨803163376099670127781627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1070884501466226837042169 803163376099670127781627)
        ·
          refine ⟨1204745064149505191672441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803163376099670127781627 1204745064149505191672441)
          ·
            refine ⟨903558798112128893754331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1204745064149505191672441 903558798112128893754331)
            ·
              refine ⟨1355338197168193340631497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903558798112128893754331 1355338197168193340631497)
              ·
                refine ⟨1016503647876145005473623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355338197168193340631497 1016503647876145005473623)
                ·
                  refine ⟨1524755471814217508210435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016503647876145005473623 1524755471814217508210435)
                  ·
                    refine ⟨2287133207721326262315653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1524755471814217508210435 2287133207721326262315653)
                    ·
                      refine ⟨428837476447748674184185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2287133207721326262315653 428837476447748674184185)
                      ·
                        rfl

theorem cell23_835158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_835158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835158 prefixEnd_835158 := by exact prefixLift 835158
  have htrace : WordTrace (prefixWord ++ tailWord_835158) baseStart_835158 baseEnd_835158 := by
    simpa [prefixWord, tailWord_835158, baseEnd_835158] using wordTrace_append hprefix tailTrace_835158
  have hstable : (prefixWord ++ tailWord_835158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835158).length < 2 ^ (prefixWord ++ tailWord_835158).sum := by decide
  have hdescent : baseEnd_835158 < baseStart_835158 := by decide
  rcases family_descends (prefixWord ++ tailWord_835158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835203 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 7]
def baseStart_835203 : Nat := 118140960795 + 835203 * 2 ^ 59
def prefixEnd_835203 : Nat := 4983230072969 + 3 ^ 40 * 835203 * 2
def baseEnd_835203 : Nat := 47651175897466777569053

theorem tailTrace_835203 : CollatzResearch.WordTrace tailWord_835203 prefixEnd_835203 47651175897466777569053 := by
  unfold tailWord_835203
  simp only [CollatzResearch.WordTrace]
  refine ⟨30462355993209647161254263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20308237328806431440836175 30462355993209647161254263)
  ·
    refine ⟨45693533989814470741881395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30462355993209647161254263 45693533989814470741881395)
    ·
      refine ⟨68540300984721706112822093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45693533989814470741881395 68540300984721706112822093)
      ·
        refine ⟨25702612869270639792308285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68540300984721706112822093 25702612869270639792308285)
        ·
          refine ⟨9638479825976489922115607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25702612869270639792308285 9638479825976489922115607)
          ·
            refine ⟨14457719738964734883173411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9638479825976489922115607 14457719738964734883173411)
            ·
              refine ⟨21686579608447102324760117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14457719738964734883173411 21686579608447102324760117)
              ·
                refine ⟨2033116838291915842946261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21686579608447102324760117 2033116838291915842946261)
                ·
                  refine ⟨47651175897466777569053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2033116838291915842946261 47651175897466777569053)
                  ·
                    rfl

theorem cell23_835203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 7].length) (baseStart_835203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835203 prefixEnd_835203 := by exact prefixLift 835203
  have htrace : WordTrace (prefixWord ++ tailWord_835203) baseStart_835203 baseEnd_835203 := by
    simpa [prefixWord, tailWord_835203, baseEnd_835203] using wordTrace_append hprefix tailTrace_835203
  have hstable : (prefixWord ++ tailWord_835203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835203).length < 2 ^ (prefixWord ++ tailWord_835203).sum := by decide
  have hdescent : baseEnd_835203 < baseStart_835203 := by decide
  rcases family_descends (prefixWord ++ tailWord_835203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835210 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_835210 : Nat := 118140960795 + 835210 * 2 ^ 59
def prefixEnd_835210 : Nat := 4983230072969 + 3 ^ 40 * 835210 * 2
def baseEnd_835210 : Nat := 428864177441782470733945

theorem tailTrace_835210 : CollatzResearch.WordTrace tailWord_835210 prefixEnd_835210 428864177441782470733945 := by
  unfold tailWord_835210
  simp only [CollatzResearch.WordTrace]
  refine ⟨7615652826046071839189771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20308407536122858237839389 7615652826046071839189771)
  ·
    refine ⟨11423479239069107758784657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7615652826046071839189771 11423479239069107758784657)
    ·
      refine ⟨8567609429301830819088493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11423479239069107758784657 8567609429301830819088493)
      ·
        refine ⟨3212853535988186557158185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8567609429301830819088493 3212853535988186557158185)
        ·
          refine ⟨2409640151991139917868639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3212853535988186557158185 2409640151991139917868639)
          ·
            refine ⟨3614460227986709876802959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409640151991139917868639 3614460227986709876802959)
            ·
              refine ⟨5421690341980064815204439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614460227986709876802959 5421690341980064815204439)
              ·
                refine ⟨8132535512970097222806659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5421690341980064815204439 8132535512970097222806659)
                ·
                  refine ⟨12198803269455145834209989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8132535512970097222806659 12198803269455145834209989)
                  ·
                    refine ⟨2287275613022839843914373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12198803269455145834209989 2287275613022839843914373)
                    ·
                      refine ⟨428864177441782470733945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2287275613022839843914373 428864177441782470733945)
                      ·
                        rfl

theorem cell23_835210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_835210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835210 prefixEnd_835210 := by exact prefixLift 835210
  have htrace : WordTrace (prefixWord ++ tailWord_835210) baseStart_835210 baseEnd_835210 := by
    simpa [prefixWord, tailWord_835210, baseEnd_835210] using wordTrace_append hprefix tailTrace_835210
  have hstable : (prefixWord ++ tailWord_835210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835210).length < 2 ^ (prefixWord ++ tailWord_835210).sum := by decide
  have hdescent : baseEnd_835210 < baseStart_835210 := by decide
  rcases family_descends (prefixWord ++ tailWord_835210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835214 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2]
def baseStart_835214 : Nat := 118140960795 + 835214 * 2 ^ 59
def prefixEnd_835214 : Nat := 4983230072969 + 3 ^ 40 * 835214 * 2
def baseEnd_835214 : Nat := 428866231364400455083927

theorem tailTrace_835214 : CollatzResearch.WordTrace tailWord_835214 prefixEnd_835214 428866231364400455083927 := by
  unfold tailWord_835214
  simp only [CollatzResearch.WordTrace]
  refine ⟨3807844649521224504988087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20308504797446530693269797 3807844649521224504988087)
  ·
    refine ⟨5711766974281836757482131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3807844649521224504988087 5711766974281836757482131)
    ·
      refine ⟨8567650461422755136223197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5711766974281836757482131 8567650461422755136223197)
      ·
        refine ⟨3212868923033533176083699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8567650461422755136223197 3212868923033533176083699)
        ·
          refine ⟨4819303384550299764125549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3212868923033533176083699 4819303384550299764125549)
          ·
            refine ⟨1807238769206362411547081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4819303384550299764125549 1807238769206362411547081)
            ·
              refine ⟨1355429076904771808660311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807238769206362411547081 1355429076904771808660311)
              ·
                refine ⟨2033143615357157712990467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355429076904771808660311 2033143615357157712990467)
                ·
                  refine ⟨3049715423035736569485701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033143615357157712990467 3049715423035736569485701)
                  ·
                    refine ⟨571821641819200606778569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3049715423035736569485701 571821641819200606778569)
                    ·
                      refine ⟨428866231364400455083927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571821641819200606778569 428866231364400455083927)
                      ·
                        rfl

theorem cell23_835214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_835214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835214 prefixEnd_835214 := by exact prefixLift 835214
  have htrace : WordTrace (prefixWord ++ tailWord_835214) baseStart_835214 baseEnd_835214 := by
    simpa [prefixWord, tailWord_835214, baseEnd_835214] using wordTrace_append hprefix tailTrace_835214
  have hstable : (prefixWord ++ tailWord_835214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835214).length < 2 ^ (prefixWord ++ tailWord_835214).sum := by decide
  have hdescent : baseEnd_835214 < baseStart_835214 := by decide
  rcases family_descends (prefixWord ++ tailWord_835214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835250 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_835250 : Nat := 118140960795 + 835250 * 2 ^ 59
def prefixEnd_835250 : Nat := 4983230072969 + 3 ^ 40 * 835250 * 2
def baseEnd_835250 : Nat := 142961572222654104744587

theorem tailTrace_835250 : CollatzResearch.WordTrace tailWord_835250 prefixEnd_835250 142961572222654104744587 := by
  unfold tailWord_835250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7616017556009843547053801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20309380149359582792143469 7616017556009843547053801)
  ·
    refine ⟨5712013167007382660290351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7616017556009843547053801 5712013167007382660290351)
    ·
      refine ⟨8568019750511073990435527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5712013167007382660290351 8568019750511073990435527)
      ·
        refine ⟨12852029625766610985653291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8568019750511073990435527 12852029625766610985653291)
        ·
          refine ⟨19278044438649916478479937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12852029625766610985653291 19278044438649916478479937)
          ·
            refine ⟨14458533328987437358859953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19278044438649916478479937 14458533328987437358859953)
            ·
              refine ⟨10843899996740578019144965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14458533328987437358859953 10843899996740578019144965)
              ·
                refine ⟨2033231249388858378589681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10843899996740578019144965 2033231249388858378589681)
                ·
                  refine ⟨1524923437041643783942261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2033231249388858378589681 1524923437041643783942261)
                  ·
                    refine ⟨142961572222654104744587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1524923437041643783942261 142961572222654104744587)
                    ·
                      rfl

theorem cell23_835250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_835250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835250 prefixEnd_835250 := by exact prefixLift 835250
  have htrace : WordTrace (prefixWord ++ tailWord_835250) baseStart_835250 baseEnd_835250 := by
    simpa [prefixWord, tailWord_835250, baseEnd_835250] using wordTrace_append hprefix tailTrace_835250
  have hstable : (prefixWord ++ tailWord_835250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835250).length < 2 ^ (prefixWord ++ tailWord_835250).sum := by decide
  have hdescent : baseEnd_835250 < baseStart_835250 := by decide
  rcases family_descends (prefixWord ++ tailWord_835250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835254 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_835254 : Nat := 118140960795 + 835254 * 2 ^ 59
def prefixEnd_835254 : Nat := 4983230072969 + 3 ^ 40 * 835254 * 2
def baseEnd_835254 : Nat := 47654085621175588731527

theorem tailTrace_835254 : CollatzResearch.WordTrace tailWord_835254 prefixEnd_835254 47654085621175588731527 := by
  unfold tailWord_835254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1904013507251555179460051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20309477410683255247573877 1904013507251555179460051)
  ·
    refine ⟨2856020260877332769190077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1904013507251555179460051 2856020260877332769190077)
    ·
      refine ⟨1071007597828999788446279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2856020260877332769190077 1071007597828999788446279)
      ·
        refine ⟨1606511396743499682669419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1071007597828999788446279 1606511396743499682669419)
        ·
          refine ⟨2409767095115249524004129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606511396743499682669419 2409767095115249524004129)
          ·
            refine ⟨1807325321336437143003097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2409767095115249524004129 1807325321336437143003097)
            ·
              refine ⟨1355493991002327857252323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807325321336437143003097 1355493991002327857252323)
              ·
                refine ⟨2033240986503491785878485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355493991002327857252323 2033240986503491785878485)
                ·
                  refine ⟨47654085621175588731527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2033240986503491785878485 47654085621175588731527)
                  ·
                    rfl

theorem cell23_835254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_835254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835254 prefixEnd_835254 := by exact prefixLift 835254
  have htrace : WordTrace (prefixWord ++ tailWord_835254) baseStart_835254 baseEnd_835254 := by
    simpa [prefixWord, tailWord_835254, baseEnd_835254] using wordTrace_append hprefix tailTrace_835254
  have hstable : (prefixWord ++ tailWord_835254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835254).length < 2 ^ (prefixWord ++ tailWord_835254).sum := by decide
  have hdescent : baseEnd_835254 < baseStart_835254 := by decide
  rcases family_descends (prefixWord ++ tailWord_835254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835280 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 5, 4]
def baseStart_835280 : Nat := 118140960795 + 835280 * 2 ^ 59
def prefixEnd_835280 : Nat := 4983230072969 + 3 ^ 40 * 835280 * 2
def baseEnd_835280 : Nat := 142966707029199065619541

theorem tailTrace_835280 : CollatzResearch.WordTrace tailWord_835280 prefixEnd_835280 142966707029199065619541 := by
  unfold tailWord_835280
  simp only [CollatzResearch.WordTrace]
  refine ⟨15232582206965344655903647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20310109609287126207871529 15232582206965344655903647)
  ·
    refine ⟨22848873310448016983855471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15232582206965344655903647 22848873310448016983855471)
    ·
      refine ⟨34273309965672025475783207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22848873310448016983855471 34273309965672025475783207)
      ·
        refine ⟨51409964948508038213674811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34273309965672025475783207 51409964948508038213674811)
        ·
          refine ⟨77114947422762057320512217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51409964948508038213674811 77114947422762057320512217)
          ·
            refine ⟨57836210567071542990384163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77114947422762057320512217 57836210567071542990384163)
            ·
              refine ⟨86754315850607314485576245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57836210567071542990384163 86754315850607314485576245)
              ·
                refine ⟨8133217110994435733022773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86754315850607314485576245 8133217110994435733022773)
                ·
                  refine ⟨762489104155728349970885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8133217110994435733022773 762489104155728349970885)
                  ·
                    refine ⟨142966707029199065619541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 762489104155728349970885 142966707029199065619541)
                    ·
                      rfl

theorem cell23_835280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 5, 4].length) (baseStart_835280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835280 prefixEnd_835280 := by exact prefixLift 835280
  have htrace : WordTrace (prefixWord ++ tailWord_835280) baseStart_835280 baseEnd_835280 := by
    simpa [prefixWord, tailWord_835280, baseEnd_835280] using wordTrace_append hprefix tailTrace_835280
  have hstable : (prefixWord ++ tailWord_835280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835280).length < 2 ^ (prefixWord ++ tailWord_835280).sum := by decide
  have hdescent : baseEnd_835280 < baseStart_835280 := by decide
  rcases family_descends (prefixWord ++ tailWord_835280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835310 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 8]
def baseStart_835310 : Nat := 118140960795 + 835310 * 2 ^ 59
def prefixEnd_835310 : Nat := 4983230072969 + 3 ^ 40 * 835310 * 2
def baseEnd_835310 : Nat := 47657280611914675498165

theorem tailTrace_835310 : CollatzResearch.WordTrace tailWord_835310 prefixEnd_835310 47657280611914675498165 := by
  unfold tailWord_835310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3808282325477750554424923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20310839069214669623599589 3808282325477750554424923)
  ·
    refine ⟨5712423488216625831637385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3808282325477750554424923 5712423488216625831637385)
    ·
      refine ⟨4284317616162469373728039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5712423488216625831637385 4284317616162469373728039)
      ·
        refine ⟨6426476424243704060592059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4284317616162469373728039 6426476424243704060592059)
        ·
          refine ⟨9639714636365556090888089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6426476424243704060592059 9639714636365556090888089)
          ·
            refine ⟨7229785977274167068166067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9639714636365556090888089 7229785977274167068166067)
            ·
              refine ⟨10844678965911250602249101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7229785977274167068166067 10844678965911250602249101)
              ·
                refine ⟨4066754612216718975843413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10844678965911250602249101 4066754612216718975843413)
                ·
                  refine ⟨47657280611914675498165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4066754612216718975843413 47657280611914675498165)
                  ·
                    rfl

theorem cell23_835310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_835310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835310 prefixEnd_835310 := by exact prefixLift 835310
  have htrace : WordTrace (prefixWord ++ tailWord_835310) baseStart_835310 baseEnd_835310 := by
    simpa [prefixWord, tailWord_835310, baseEnd_835310] using wordTrace_append hprefix tailTrace_835310
  have hstable : (prefixWord ++ tailWord_835310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835310).length < 2 ^ (prefixWord ++ tailWord_835310).sum := by decide
  have hdescent : baseEnd_835310 < baseStart_835310 := by decide
  rcases family_descends (prefixWord ++ tailWord_835310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835320 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 2, 5, 3]
def baseStart_835320 : Nat := 118140960795 + 835320 * 2 ^ 59
def prefixEnd_835320 : Nat := 4983230072969 + 3 ^ 40 * 835320 * 2
def baseEnd_835320 : Nat := 428920660313777040358439

theorem tailTrace_835320 : CollatzResearch.WordTrace tailWord_835320 prefixEnd_835320 428920660313777040358439 := by
  unfold tailWord_835320
  simp only [CollatzResearch.WordTrace]
  refine ⟨15233311666892888071631707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20311082222523850762175609 15233311666892888071631707)
  ·
    refine ⟨22849967500339332107447561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15233311666892888071631707 22849967500339332107447561)
    ·
      refine ⟨17137475625254499080585671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22849967500339332107447561 17137475625254499080585671)
      ·
        refine ⟨25706213437881748620878507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17137475625254499080585671 25706213437881748620878507)
        ·
          refine ⟨38559320156822622931317761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25706213437881748620878507 38559320156822622931317761)
          ·
            refine ⟨28919490117616967198488321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38559320156822622931317761 28919490117616967198488321)
            ·
              refine ⟨21689617588212725398866241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28919490117616967198488321 21689617588212725398866241)
              ·
                refine ⟨16267213191159544049149681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21689617588212725398866241 16267213191159544049149681)
                ·
                  refine ⟨12200409893369658036862261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16267213191159544049149681 12200409893369658036862261)
                  ·
                    refine ⟨1143788427503405440955837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12200409893369658036862261 1143788427503405440955837)
                    ·
                      refine ⟨428920660313777040358439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1143788427503405440955837 428920660313777040358439)
                      ·
                        rfl

theorem cell23_835320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_835320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835320 prefixEnd_835320 := by exact prefixLift 835320
  have htrace : WordTrace (prefixWord ++ tailWord_835320) baseStart_835320 baseEnd_835320 := by
    simpa [prefixWord, tailWord_835320, baseEnd_835320] using wordTrace_append hprefix tailTrace_835320
  have hstable : (prefixWord ++ tailWord_835320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835320).length < 2 ^ (prefixWord ++ tailWord_835320).sum := by decide
  have hdescent : baseEnd_835320 < baseStart_835320 := by decide
  rcases family_descends (prefixWord ++ tailWord_835320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835327 : List Nat := [1, 1, 2, 2, 1, 3, 6, 1, 6]
def baseStart_835327 : Nat := 118140960795 + 835327 * 2 ^ 59
def prefixEnd_835327 : Nat := 4983230072969 + 3 ^ 40 * 835327 * 2
def baseEnd_835327 : Nat := 47658250519817612552323

theorem tailTrace_835327 : CollatzResearch.WordTrace tailWord_835327 prefixEnd_835327 47658250519817612552323 := by
  unfold tailWord_835327
  simp only [CollatzResearch.WordTrace]
  refine ⟨30466878644760416338768235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20311252429840277559178823 30466878644760416338768235)
  ·
    refine ⟨45700317967140624508152353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30466878644760416338768235 45700317967140624508152353)
    ·
      refine ⟨34275238475355468381114265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45700317967140624508152353 34275238475355468381114265)
      ·
        refine ⟨25706428856516601285835699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34275238475355468381114265 25706428856516601285835699)
        ·
          refine ⟨38559643284774901928753549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25706428856516601285835699 38559643284774901928753549)
          ·
            refine ⟨14459866231790588223282581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38559643284774901928753549 14459866231790588223282581)
            ·
              refine ⟨677806229615183822966371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14459866231790588223282581 677806229615183822966371)
              ·
                refine ⟨1016709344422775734449557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677806229615183822966371 1016709344422775734449557)
                ·
                  refine ⟨47658250519817612552323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1016709344422775734449557 47658250519817612552323)
                  ·
                    rfl

theorem cell23_835327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 6].length) (baseStart_835327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835327 prefixEnd_835327 := by exact prefixLift 835327
  have htrace : WordTrace (prefixWord ++ tailWord_835327) baseStart_835327 baseEnd_835327 := by
    simpa [prefixWord, tailWord_835327, baseEnd_835327] using wordTrace_append hprefix tailTrace_835327
  have hstable : (prefixWord ++ tailWord_835327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835327).length < 2 ^ (prefixWord ++ tailWord_835327).sum := by decide
  have hdescent : baseEnd_835327 < baseStart_835327 := by decide
  rcases family_descends (prefixWord ++ tailWord_835327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835337 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 5, 1, 3]
def baseStart_835337 : Nat := 118140960795 + 835337 * 2 ^ 59
def prefixEnd_835337 : Nat := 4983230072969 + 3 ^ 40 * 835337 * 2
def baseEnd_835337 : Nat := 428929389484903473845861

theorem tailTrace_835337 : CollatzResearch.WordTrace tailWord_835337 prefixEnd_835337 428929389484903473845861 := by
  unfold tailWord_835337
  simp only [CollatzResearch.WordTrace]
  refine ⟨30467243374724188046632265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20311495583149458697754843 30467243374724188046632265)
  ·
    refine ⟨22850432531043141034974199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30467243374724188046632265 22850432531043141034974199)
    ·
      refine ⟨34275648796564711552461299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22850432531043141034974199 34275648796564711552461299)
      ·
        refine ⟨51413473194847067328691949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34275648796564711552461299 51413473194847067328691949)
        ·
          refine ⟨19280052448067650248259481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51413473194847067328691949 19280052448067650248259481)
          ·
            refine ⟨14460039336050737686194611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19280052448067650248259481 14460039336050737686194611)
            ·
              refine ⟨21690059004076106529291917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14460039336050737686194611 21690059004076106529291917)
              ·
                refine ⟨8133772126528539948484469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21690059004076106529291917 8133772126528539948484469)
                ·
                  refine ⟨762541136862050620170419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8133772126528539948484469 762541136862050620170419)
                  ·
                    refine ⟨1143811705293075930255629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 762541136862050620170419 1143811705293075930255629)
                    ·
                      refine ⟨428929389484903473845861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1143811705293075930255629 428929389484903473845861)
                      ·
                        rfl

theorem cell23_835337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 5, 1, 3].length) (baseStart_835337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835337 prefixEnd_835337 := by exact prefixLift 835337
  have htrace : WordTrace (prefixWord ++ tailWord_835337) baseStart_835337 baseEnd_835337 := by
    simpa [prefixWord, tailWord_835337, baseEnd_835337] using wordTrace_append hprefix tailTrace_835337
  have hstable : (prefixWord ++ tailWord_835337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835337).length < 2 ^ (prefixWord ++ tailWord_835337).sum := by decide
  have hdescent : baseEnd_835337 < baseStart_835337 := by decide
  rcases family_descends (prefixWord ++ tailWord_835337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835377 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_835377 : Nat := 118140960795 + 835377 * 2 ^ 59
def prefixEnd_835377 : Nat := 4983230072969 + 3 ^ 40 * 835377 * 2
def baseEnd_835377 : Nat := 428949928711083317345677

theorem tailTrace_835377 : CollatzResearch.WordTrace tailWord_835377 prefixEnd_835377 428949928711083317345677 := by
  unfold tailWord_835377
  simp only [CollatzResearch.WordTrace]
  refine ⟨30468702294579274878088385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20312468196386183252058923 30468702294579274878088385)
  ·
    refine ⟨22851526720934456158566289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30468702294579274878088385 22851526720934456158566289)
    ·
      refine ⟨17138645040700842118924717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22851526720934456158566289 17138645040700842118924717)
      ·
        refine ⟨6426991890262815794596769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17138645040700842118924717 6426991890262815794596769)
        ·
          refine ⟨4820243917697111845947577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6426991890262815794596769 4820243917697111845947577)
          ·
            refine ⟨3615182938272833884460683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4820243917697111845947577 3615182938272833884460683)
            ·
              refine ⟨5422774407409250826691025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3615182938272833884460683 5422774407409250826691025)
              ·
                refine ⟨4067080805556938120018269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5422774407409250826691025 4067080805556938120018269)
                ·
                  refine ⟨1525155302083851795006851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4067080805556938120018269 1525155302083851795006851)
                  ·
                    refine ⟨2287732953125777692510277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1525155302083851795006851 2287732953125777692510277)
                    ·
                      refine ⟨428949928711083317345677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2287732953125777692510277 428949928711083317345677)
                      ·
                        rfl

theorem cell23_835377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_835377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835377 prefixEnd_835377 := by exact prefixLift 835377
  have htrace : WordTrace (prefixWord ++ tailWord_835377) baseStart_835377 baseEnd_835377 := by
    simpa [prefixWord, tailWord_835377, baseEnd_835377] using wordTrace_append hprefix tailTrace_835377
  have hstable : (prefixWord ++ tailWord_835377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835377).length < 2 ^ (prefixWord ++ tailWord_835377).sum := by decide
  have hdescent : baseEnd_835377 < baseStart_835377 := by decide
  rcases family_descends (prefixWord ++ tailWord_835377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835397 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 3, 2, 3]
def baseStart_835397 : Nat := 118140960795 + 835397 * 2 ^ 59
def prefixEnd_835397 : Nat := 4983230072969 + 3 ^ 40 * 835397 * 2
def baseEnd_835397 : Nat := 428960198324173239095585

theorem tailTrace_835397 : CollatzResearch.WordTrace tailWord_835397 prefixEnd_835397 428960198324173239095585 := by
  unfold tailWord_835397
  simp only [CollatzResearch.WordTrace]
  refine ⟨30469431754506818293816445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20312954503004545529210963 30469431754506818293816445)
  ·
    refine ⟨11426036907940056860181167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30469431754506818293816445 11426036907940056860181167)
    ·
      refine ⟨17139055361910085290271751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11426036907940056860181167 17139055361910085290271751)
      ·
        refine ⟨25708583042865127935407627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17139055361910085290271751 25708583042865127935407627)
        ·
          refine ⟨38562874564297691903111441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25708583042865127935407627 38562874564297691903111441)
          ·
            refine ⟨28922155923223268927333581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38562874564297691903111441 28922155923223268927333581)
            ·
              refine ⟨10845808471208725847750093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28922155923223268927333581 10845808471208725847750093)
              ·
                refine ⟨4067178176703272192906285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10845808471208725847750093 4067178176703272192906285)
                ·
                  refine ⟨1525191816263727072339857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4067178176703272192906285 1525191816263727072339857)
                  ·
                    refine ⟨1143893862197795304254893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1525191816263727072339857 1143893862197795304254893)
                    ·
                      refine ⟨428960198324173239095585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1143893862197795304254893 428960198324173239095585)
                      ·
                        rfl

theorem cell23_835397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_835397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835397 prefixEnd_835397 := by exact prefixLift 835397
  have htrace : WordTrace (prefixWord ++ tailWord_835397) baseStart_835397 baseEnd_835397 := by
    simpa [prefixWord, tailWord_835397, baseEnd_835397] using wordTrace_append hprefix tailTrace_835397
  have hstable : (prefixWord ++ tailWord_835397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835397).length < 2 ^ (prefixWord ++ tailWord_835397).sum := by decide
  have hdescent : baseEnd_835397 < baseStart_835397 := by decide
  rcases family_descends (prefixWord ++ tailWord_835397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835398 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_835398 : Nat := 118140960795 + 835398 * 2 ^ 59
def prefixEnd_835398 : Nat := 4983230072969 + 3 ^ 40 * 835398 * 2
def baseEnd_835398 : Nat := 428960711804827735183081

theorem tailTrace_835398 : CollatzResearch.WordTrace tailWord_835398 prefixEnd_835398 428960711804827735183081 := by
  unfold tailWord_835398
  simp only [CollatzResearch.WordTrace]
  refine ⟨952170882109474858268839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20312978818335463643068565 952170882109474858268839)
  ·
    refine ⟨1428256323164212287403259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 952170882109474858268839 1428256323164212287403259)
    ·
      refine ⟨2142384484746318431104889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1428256323164212287403259 2142384484746318431104889)
      ·
        refine ⟨1606788363559738823328667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2142384484746318431104889 1606788363559738823328667)
        ·
          refine ⟨2410182545339608234993001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606788363559738823328667 2410182545339608234993001)
          ·
            refine ⟨1807636909004706176244751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2410182545339608234993001 1807636909004706176244751)
            ·
              refine ⟨2711455363507059264367127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1807636909004706176244751 2711455363507059264367127)
              ·
                refine ⟨4067183045260588896550691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2711455363507059264367127 4067183045260588896550691)
                ·
                  refine ⟨6100774567890883344826037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4067183045260588896550691 6100774567890883344826037)
                  ·
                    refine ⟨571947615739770313577441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6100774567890883344826037 571947615739770313577441)
                    ·
                      refine ⟨428960711804827735183081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571947615739770313577441 428960711804827735183081)
                      ·
                        rfl

theorem cell23_835398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_835398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835398 prefixEnd_835398 := by exact prefixLift 835398
  have htrace : WordTrace (prefixWord ++ tailWord_835398) baseStart_835398 baseEnd_835398 := by
    simpa [prefixWord, tailWord_835398, baseEnd_835398] using wordTrace_append hprefix tailTrace_835398
  have hstable : (prefixWord ++ tailWord_835398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835398).length < 2 ^ (prefixWord ++ tailWord_835398).sum := by decide
  have hdescent : baseEnd_835398 < baseStart_835398 := by decide
  rcases family_descends (prefixWord ++ tailWord_835398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835405 : List Nat := [1, 6, 1, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_835405 : Nat := 118140960795 + 835405 * 2 ^ 59
def prefixEnd_835405 : Nat := 4983230072969 + 3 ^ 40 * 835405 * 2
def baseEnd_835405 : Nat := 428964306169409207795549

theorem tailTrace_835405 : CollatzResearch.WordTrace tailWord_835405 prefixEnd_835405 428964306169409207795549 := by
  unfold tailWord_835405
  simp only [CollatzResearch.WordTrace]
  refine ⟨30469723538477835660107669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20313149025651890440071779 30469723538477835660107669)
  ·
    refine ⟨1428268290866148546567547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30469723538477835660107669 1428268290866148546567547)
    ·
      refine ⟨2142402436299222819851321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1428268290866148546567547 2142402436299222819851321)
      ·
        refine ⟨1606801827224417114888491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2142402436299222819851321 1606801827224417114888491)
        ·
          refine ⟨2410202740836625672332737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606801827224417114888491 2410202740836625672332737)
          ·
            refine ⟨1807652055627469254249553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2410202740836625672332737 1807652055627469254249553)
            ·
              refine ⟨1355739041720601940687165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807652055627469254249553 1355739041720601940687165)
              ·
                refine ⟨508402140645225727757687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1355739041720601940687165 508402140645225727757687)
                ·
                  refine ⟨762603210967838591636531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508402140645225727757687 762603210967838591636531)
                  ·
                    refine ⟨1143904816451757887454797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 762603210967838591636531 1143904816451757887454797)
                    ·
                      refine ⟨428964306169409207795549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1143904816451757887454797 428964306169409207795549)
                      ·
                        rfl

theorem cell23_835405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_835405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835405 prefixEnd_835405 := by exact prefixLift 835405
  have htrace : WordTrace (prefixWord ++ tailWord_835405) baseStart_835405 baseEnd_835405 := by
    simpa [prefixWord, tailWord_835405, baseEnd_835405] using wordTrace_append hprefix tailTrace_835405
  have hstable : (prefixWord ++ tailWord_835405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835405).length < 2 ^ (prefixWord ++ tailWord_835405).sum := by decide
  have hdescent : baseEnd_835405 < baseStart_835405 := by decide
  rcases family_descends (prefixWord ++ tailWord_835405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835428 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 3, 2, 2]
def baseStart_835428 : Nat := 118140960795 + 835428 * 2 ^ 59
def prefixEnd_835428 : Nat := 4983230072969 + 3 ^ 40 * 835428 * 2
def baseEnd_835428 : Nat := 428976116224462617807943

theorem tailTrace_835428 : CollatzResearch.WordTrace tailWord_835428 prefixEnd_835428 428976116224462617807943 := by
  unfold tailWord_835428
  simp only [CollatzResearch.WordTrace]
  refine ⟨15235281208697255294097469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20313708278263007058796625 15235281208697255294097469)
  ·
    refine ⟨5713230453261470735286551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15235281208697255294097469 5713230453261470735286551)
    ·
      refine ⟨8569845679892206102929827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5713230453261470735286551 8569845679892206102929827)
      ·
        refine ⟨12854768519838309154394741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8569845679892206102929827 12854768519838309154394741)
        ·
          refine ⟨1205134548734841483224507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12854768519838309154394741 1205134548734841483224507)
          ·
            refine ⟨1807701823102262224836761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205134548734841483224507 1807701823102262224836761)
            ·
              refine ⟨1355776367326696668627571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807701823102262224836761 1355776367326696668627571)
              ·
                refine ⟨2033664550990045002941357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355776367326696668627571 2033664550990045002941357)
                ·
                  refine ⟨762624206621266876103009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2033664550990045002941357 762624206621266876103009)
                  ·
                    refine ⟨571968154965950157077257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 762624206621266876103009 571968154965950157077257)
                    ·
                      refine ⟨428976116224462617807943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 571968154965950157077257 428976116224462617807943)
                      ·
                        rfl

theorem cell23_835428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_835428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835428 prefixEnd_835428 := by exact prefixLift 835428
  have htrace : WordTrace (prefixWord ++ tailWord_835428) baseStart_835428 baseEnd_835428 := by
    simpa [prefixWord, tailWord_835428, baseEnd_835428] using wordTrace_append hprefix tailTrace_835428
  have hstable : (prefixWord ++ tailWord_835428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835428).length < 2 ^ (prefixWord ++ tailWord_835428).sum := by decide
  have hdescent : baseEnd_835428 < baseStart_835428 := by decide
  rcases family_descends (prefixWord ++ tailWord_835428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835438 : List Nat := [4, 1, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_835438 : Nat := 118140960795 + 835438 * 2 ^ 59
def prefixEnd_835438 : Nat := 4983230072969 + 3 ^ 40 * 835438 * 2
def baseEnd_835438 : Nat := 142993750343669192894299

theorem tailTrace_835438 : CollatzResearch.WordTrace tailWord_835438 prefixEnd_835438 142993750343669192894299 := by
  unfold tailWord_835438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3808865893419785287007371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20313951431572188197372645 3808865893419785287007371)
  ·
    refine ⟨5713298840129677930511057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3808865893419785287007371 5713298840129677930511057)
    ·
      refine ⟨4284974130097258447883293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5713298840129677930511057 4284974130097258447883293)
      ·
        refine ⟨1606865298786471917956235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4284974130097258447883293 1606865298786471917956235)
        ·
          refine ⟨2410297948179707876934353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606865298786471917956235 2410297948179707876934353)
          ·
            refine ⟨1807723461134780907700765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2410297948179707876934353 1807723461134780907700765)
            ·
              refine ⟨677896297925542840387787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1807723461134780907700765 677896297925542840387787)
              ·
                refine ⟨1016844446888314260581681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677896297925542840387787 1016844446888314260581681)
                ·
                  refine ⟨762633335166235695436261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1016844446888314260581681 762633335166235695436261)
                  ·
                    refine ⟨142993750343669192894299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 762633335166235695436261 142993750343669192894299)
                    ·
                      rfl

theorem cell23_835438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_835438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835438 prefixEnd_835438 := by exact prefixLift 835438
  have htrace : WordTrace (prefixWord ++ tailWord_835438) baseStart_835438 baseEnd_835438 := by
    simpa [prefixWord, tailWord_835438, baseEnd_835438] using wordTrace_append hprefix tailTrace_835438
  have hstable : (prefixWord ++ tailWord_835438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835438).length < 2 ^ (prefixWord ++ tailWord_835438).sum := by decide
  have hdescent : baseEnd_835438 < baseStart_835438 := by decide
  rcases family_descends (prefixWord ++ tailWord_835438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835495 : List Nat := [1, 1, 6, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_835495 : Nat := 118140960795 + 835495 * 2 ^ 59
def prefixEnd_835495 : Nat := 4983230072969 + 3 ^ 40 * 835495 * 2
def baseEnd_835495 : Nat := 429010519428313855670135

theorem tailTrace_835495 : CollatzResearch.WordTrace tailWord_835495 prefixEnd_835495 429010519428313855670135 := by
  unfold tailWord_835495
  simp only [CollatzResearch.WordTrace]
  refine ⟨30473006108151781030883939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20315337405434520687255959 30473006108151781030883939)
  ·
    refine ⟨45709509162227671546325909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30473006108151781030883939 45709509162227671546325909)
    ·
      refine ⟨2142633241979422103734027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45709509162227671546325909 2142633241979422103734027)
      ·
        refine ⟨3213949862969133155601041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142633241979422103734027 3213949862969133155601041)
        ·
          refine ⟨2410462397226849866700781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3213949862969133155601041 2410462397226849866700781)
          ·
            refine ⟨903923398960068700012793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2410462397226849866700781 903923398960068700012793)
            ·
              refine ⟨677942549220051525009595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 903923398960068700012793 677942549220051525009595)
              ·
                refine ⟨1016913823830077287514393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677942549220051525009595 1016913823830077287514393)
                ·
                  refine ⟨762685367872557965635795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1016913823830077287514393 762685367872557965635795)
                  ·
                    refine ⟨1144028051808836948453693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 762685367872557965635795 1144028051808836948453693)
                    ·
                      refine ⟨429010519428313855670135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1144028051808836948453693 429010519428313855670135)
                      ·
                        rfl

theorem cell23_835495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_835495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835495 prefixEnd_835495 := by exact prefixLift 835495
  have htrace : WordTrace (prefixWord ++ tailWord_835495) baseStart_835495 baseEnd_835495 := by
    simpa [prefixWord, tailWord_835495, baseEnd_835495] using wordTrace_append hprefix tailTrace_835495
  have hstable : (prefixWord ++ tailWord_835495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835495).length < 2 ^ (prefixWord ++ tailWord_835495).sum := by decide
  have hdescent : baseEnd_835495 < baseStart_835495 := by decide
  rcases family_descends (prefixWord ++ tailWord_835495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835534 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_835534 : Nat := 118140960795 + 835534 * 2 ^ 59
def prefixEnd_835534 : Nat := 4983230072969 + 3 ^ 40 * 835534 * 2
def baseEnd_835534 : Nat := 429030545173839203082455

theorem tailTrace_835534 : CollatzResearch.WordTrace tailWord_835534 prefixEnd_835534 429030545173839203082455 := by
  unfold tailWord_835534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3809303569376311336444207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20316285703340327127702437 3809303569376311336444207)
  ·
    refine ⟨5713955354064467004666311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3809303569376311336444207 5713955354064467004666311)
    ·
      refine ⟨8570933031096700506999467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5713955354064467004666311 8570933031096700506999467)
      ·
        refine ⟨12856399546645050760499201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8570933031096700506999467 12856399546645050760499201)
        ·
          refine ⟨9642299659983788070374401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12856399546645050760499201 9642299659983788070374401)
          ·
            refine ⟨7231724744987841052780801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9642299659983788070374401 7231724744987841052780801)
            ·
              refine ⟨5423793558740880789585601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7231724744987841052780801 5423793558740880789585601)
              ·
                refine ⟨4067845169055660592189201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5423793558740880789585601 4067845169055660592189201)
                ·
                  refine ⟨3050883876791745444141901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4067845169055660592189201 3050883876791745444141901)
                  ·
                    refine ⟨1144081453796904541553213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3050883876791745444141901 1144081453796904541553213)
                    ·
                      refine ⟨429030545173839203082455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1144081453796904541553213 429030545173839203082455)
                      ·
                        rfl

theorem cell23_835534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_835534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835534 prefixEnd_835534 := by exact prefixLift 835534
  have htrace : WordTrace (prefixWord ++ tailWord_835534) baseStart_835534 baseEnd_835534 := by
    simpa [prefixWord, tailWord_835534, baseEnd_835534] using wordTrace_append hprefix tailTrace_835534
  have hstable : (prefixWord ++ tailWord_835534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835534).length < 2 ^ (prefixWord ++ tailWord_835534).sum := by decide
  have hdescent : baseEnd_835534 < baseStart_835534 := by decide
  rcases family_descends (prefixWord ++ tailWord_835534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835537 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 4, 5]
def baseStart_835537 : Nat := 118140960795 + 835537 * 2 ^ 59
def prefixEnd_835537 : Nat := 4983230072969 + 3 ^ 40 * 835537 * 2
def baseEnd_835537 : Nat := 143010695205267563781647

theorem tailTrace_835537 : CollatzResearch.WordTrace tailWord_835537 prefixEnd_835537 143010695205267563781647 := by
  unfold tailWord_835537
  simp only [CollatzResearch.WordTrace]
  refine ⟨30474537973999622203912865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20316358649333081469275243 30474537973999622203912865)
  ·
    refine ⟨22855903480499716652934649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30474537973999622203912865 22855903480499716652934649)
    ·
      refine ⟨17141927610374787489700987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22855903480499716652934649 17141927610374787489700987)
      ·
        refine ⟨25712891415562181234551481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17141927610374787489700987 25712891415562181234551481)
        ·
          refine ⟨19284668561671635925913611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25712891415562181234551481 19284668561671635925913611)
          ·
            refine ⟨28927002842507453888870417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19284668561671635925913611 28927002842507453888870417)
            ·
              refine ⟨21695252131880590416652813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28927002842507453888870417 21695252131880590416652813)
              ·
                refine ⟨8135719549455221406244805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21695252131880590416652813 8135719549455221406244805)
                ·
                  refine ⟨1525447415522854013670901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8135719549455221406244805 1525447415522854013670901)
                  ·
                    refine ⟨143010695205267563781647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1525447415522854013670901 143010695205267563781647)
                    ·
                      rfl

theorem cell23_835537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_835537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835537 prefixEnd_835537 := by exact prefixLift 835537
  have htrace : WordTrace (prefixWord ++ tailWord_835537) baseStart_835537 baseEnd_835537 := by
    simpa [prefixWord, tailWord_835537, baseEnd_835537] using wordTrace_append hprefix tailTrace_835537
  have hstable : (prefixWord ++ tailWord_835537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835537).length < 2 ^ (prefixWord ++ tailWord_835537).sum := by decide
  have hdescent : baseEnd_835537 < baseStart_835537 := by decide
  rcases family_descends (prefixWord ++ tailWord_835537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835541 : List Nat := [1, 3, 2, 3, 2, 2, 1, 4, 5]
def baseStart_835541 : Nat := 118140960795 + 835541 * 2 ^ 59
def prefixEnd_835541 : Nat := 4983230072969 + 3 ^ 40 * 835541 * 2
def baseEnd_835541 : Nat := 47670459948713408410547

theorem tailTrace_835541 : CollatzResearch.WordTrace tailWord_835541 prefixEnd_835541 47670459948713408410547 := by
  unfold tailWord_835541
  simp only [CollatzResearch.WordTrace]
  refine ⟨30474683865985130887058477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20316455910656753924705651 30474683865985130887058477)
  ·
    refine ⟨11428006449744424082646929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30474683865985130887058477 11428006449744424082646929)
    ·
      refine ⟨8571004837308318061985197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11428006449744424082646929 8571004837308318061985197)
      ·
        refine ⟨3214126813990619273244449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8571004837308318061985197 3214126813990619273244449)
        ·
          refine ⟨2410595110492964454933337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3214126813990619273244449 2410595110492964454933337)
          ·
            refine ⟨1807946332869723341200003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2410595110492964454933337 1807946332869723341200003)
            ·
              refine ⟨2711919499304585011800005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1807946332869723341200003 2711919499304585011800005)
              ·
                refine ⟨508484906119609689712501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2711919499304585011800005 508484906119609689712501)
                ·
                  refine ⟨47670459948713408410547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 508484906119609689712501 47670459948713408410547)
                  ·
                    rfl

theorem cell23_835541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 5].length) (baseStart_835541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835541 prefixEnd_835541 := by exact prefixLift 835541
  have htrace : WordTrace (prefixWord ++ tailWord_835541) baseStart_835541 baseEnd_835541 := by
    simpa [prefixWord, tailWord_835541, baseEnd_835541] using wordTrace_append hprefix tailTrace_835541
  have hstable : (prefixWord ++ tailWord_835541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835541).length < 2 ^ (prefixWord ++ tailWord_835541).sum := by decide
  have hdescent : baseEnd_835541 < baseStart_835541 := by decide
  rcases family_descends (prefixWord ++ tailWord_835541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835544 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 1, 7, 2]
def baseStart_835544 : Nat := 118140960795 + 835544 * 2 ^ 59
def prefixEnd_835544 : Nat := 4983230072969 + 3 ^ 40 * 835544 * 2
def baseEnd_835544 : Nat := 429035679980384163957409

theorem tailTrace_835544 : CollatzResearch.WordTrace tailWord_835544 prefixEnd_835544 429035679980384163957409 := by
  unfold tailWord_835544
  simp only [CollatzResearch.WordTrace]
  refine ⟨15237396642487131199708843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20316528856649508266278457 15237396642487131199708843)
  ·
    refine ⟨22856094963730696799563265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15237396642487131199708843 22856094963730696799563265)
    ·
      refine ⟨17142071222798022599672449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22856094963730696799563265 17142071222798022599672449)
      ·
        refine ⟨12856553417098516949754337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17142071222798022599672449 12856553417098516949754337)
        ·
          refine ⟨9642415062823887712315753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12856553417098516949754337 9642415062823887712315753)
          ·
            refine ⟨7231811297117915784236815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9642415062823887712315753 7231811297117915784236815)
            ·
              refine ⟨10847716945676873676355223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7231811297117915784236815 10847716945676873676355223)
              ·
                refine ⟨16271575418515310514532835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10847716945676873676355223 16271575418515310514532835)
                ·
                  refine ⟨24407363127772965771799253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16271575418515310514532835 24407363127772965771799253)
                  ·
                    refine ⟨572047573307178885276545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24407363127772965771799253 572047573307178885276545)
                    ·
                      refine ⟨429035679980384163957409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 572047573307178885276545 429035679980384163957409)
                      ·
                        rfl

theorem cell23_835544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_835544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835544 prefixEnd_835544 := by exact prefixLift 835544
  have htrace : WordTrace (prefixWord ++ tailWord_835544) baseStart_835544 baseEnd_835544 := by
    simpa [prefixWord, tailWord_835544, baseEnd_835544] using wordTrace_append hprefix tailTrace_835544
  have hstable : (prefixWord ++ tailWord_835544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835544).length < 2 ^ (prefixWord ++ tailWord_835544).sum := by decide
  have hdescent : baseEnd_835544 < baseStart_835544 := by decide
  rcases family_descends (prefixWord ++ tailWord_835544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835587 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 4]
def baseStart_835587 : Nat := 118140960795 + 835587 * 2 ^ 59
def prefixEnd_835587 : Nat := 4983230072969 + 3 ^ 40 * 835587 * 2
def baseEnd_835587 : Nat := 429057759648527495719711

theorem tailTrace_835587 : CollatzResearch.WordTrace tailWord_835587 prefixEnd_835587 429057759648527495719711 := by
  unfold tailWord_835587
  simp only [CollatzResearch.WordTrace]
  refine ⟨30476361623818480743233015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20317574415878987162155343 30476361623818480743233015)
  ·
    refine ⟨45714542435727721114849523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30476361623818480743233015 45714542435727721114849523)
    ·
      refine ⟨68571813653591581672274285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45714542435727721114849523 68571813653591581672274285)
      ·
        refine ⟨25714430120096843127102857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68571813653591581672274285 25714430120096843127102857)
        ·
          refine ⟨19285822590072632345327143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25714430120096843127102857 19285822590072632345327143)
          ·
            refine ⟨28928733885108948517990715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19285822590072632345327143 28928733885108948517990715)
            ·
              refine ⟨43393100827663422776986073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28928733885108948517990715 43393100827663422776986073)
              ·
                refine ⟨32544825620747567082739555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43393100827663422776986073 32544825620747567082739555)
                ·
                  refine ⟨48817238431121350624109333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32544825620747567082739555 48817238431121350624109333)
                  ·
                    refine ⟨2288308051458813310505125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48817238431121350624109333 2288308051458813310505125)
                    ·
                      refine ⟨429057759648527495719711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2288308051458813310505125 429057759648527495719711)
                      ·
                        rfl

theorem cell23_835587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_835587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835587 prefixEnd_835587 := by exact prefixLift 835587
  have htrace : WordTrace (prefixWord ++ tailWord_835587) baseStart_835587 baseEnd_835587 := by
    simpa [prefixWord, tailWord_835587, baseEnd_835587] using wordTrace_append hprefix tailTrace_835587
  have hstable : (prefixWord ++ tailWord_835587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835587).length < 2 ^ (prefixWord ++ tailWord_835587).sum := by decide
  have hdescent : baseEnd_835587 < baseStart_835587 := by decide
  rcases family_descends (prefixWord ++ tailWord_835587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835591 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 2, 4, 2]
def baseStart_835591 : Nat := 118140960795 + 835591 * 2 ^ 59
def prefixEnd_835591 : Nat := 4983230072969 + 3 ^ 40 * 835591 * 2
def baseEnd_835591 : Nat := 429059813571145480069693

theorem tailTrace_835591 : CollatzResearch.WordTrace tailWord_835591 prefixEnd_835591 429059813571145480069693 := by
  unfold tailWord_835591
  simp only [CollatzResearch.WordTrace]
  refine ⟨30476507515803989426378627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20317671677202659617585751 30476507515803989426378627)
  ·
    refine ⟨45714761273705984139567941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30476507515803989426378627 45714761273705984139567941)
    ·
      refine ⟨8571517738819872026168989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45714761273705984139567941 8571517738819872026168989)
      ·
        refine ⟨3214319152057452009813371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8571517738819872026168989 3214319152057452009813371)
        ·
          refine ⟨4821478728086178014720057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3214319152057452009813371 4821478728086178014720057)
          ·
            refine ⟨3616109046064633511040043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4821478728086178014720057 3616109046064633511040043)
            ·
              refine ⟨5424163569096950266560065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3616109046064633511040043 5424163569096950266560065)
              ·
                refine ⟨4068122676822712699920049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5424163569096950266560065 4068122676822712699920049)
                ·
                  refine ⟨3051092007617034524940037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4068122676822712699920049 3051092007617034524940037)
                  ·
                    refine ⟨572079751428193973426257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3051092007617034524940037 572079751428193973426257)
                    ·
                      refine ⟨429059813571145480069693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 572079751428193973426257 429059813571145480069693)
                      ·
                        rfl

theorem cell23_835591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_835591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835591 prefixEnd_835591 := by exact prefixLift 835591
  have htrace : WordTrace (prefixWord ++ tailWord_835591) baseStart_835591 baseEnd_835591 := by
    simpa [prefixWord, tailWord_835591, baseEnd_835591] using wordTrace_append hprefix tailTrace_835591
  have hstable : (prefixWord ++ tailWord_835591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835591).length < 2 ^ (prefixWord ++ tailWord_835591).sum := by decide
  have hdescent : baseEnd_835591 < baseStart_835591 := by decide
  rcases family_descends (prefixWord ++ tailWord_835591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835661 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_835661 : Nat := 118140960795 + 835661 * 2 ^ 59
def prefixEnd_835661 : Nat := 4983230072969 + 3 ^ 40 * 835661 * 2
def baseEnd_835661 : Nat := 143031919072320068731457

theorem tailTrace_835661 : CollatzResearch.WordTrace tailWord_835661 prefixEnd_835661 143031919072320068731457 := by
  unfold tailWord_835661
  simp only [CollatzResearch.WordTrace]
  refine ⟨30479060625550391381426837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20319373750366927587617891 30479060625550391381426837)
  ·
    refine ⟨1428705966822674596004383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30479060625550391381426837 1428705966822674596004383)
    ·
      refine ⟨2143058950234011894006575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1428705966822674596004383 2143058950234011894006575)
      ·
        refine ⟨3214588425351017841009863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2143058950234011894006575 3214588425351017841009863)
        ·
          refine ⟨4821882638026526761514795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3214588425351017841009863 4821882638026526761514795)
          ·
            refine ⟨7232823957039790142272193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4821882638026526761514795 7232823957039790142272193)
            ·
              refine ⟨5424617967779842606704145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7232823957039790142272193 5424617967779842606704145)
              ·
                refine ⟨4068463475834881955028109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5424617967779842606704145 4068463475834881955028109)
                ·
                  refine ⟨1525673803438080733135541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4068463475834881955028109 1525673803438080733135541)
                  ·
                    refine ⟨143031919072320068731457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1525673803438080733135541 143031919072320068731457)
                    ·
                      rfl

theorem cell23_835661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_835661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835661 prefixEnd_835661 := by exact prefixLift 835661
  have htrace : WordTrace (prefixWord ++ tailWord_835661) baseStart_835661 baseEnd_835661 := by
    simpa [prefixWord, tailWord_835661, baseEnd_835661] using wordTrace_append hprefix tailTrace_835661
  have hstable : (prefixWord ++ tailWord_835661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835661).length < 2 ^ (prefixWord ++ tailWord_835661).sum := by decide
  have hdescent : baseEnd_835661 < baseStart_835661 := by decide
  rcases family_descends (prefixWord ++ tailWord_835661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835674 : List Nat := [3, 1, 1, 2, 1, 1, 4, 3, 1, 6]
def baseStart_835674 : Nat := 118140960795 + 835674 * 2 ^ 59
def prefixEnd_835674 : Nat := 4983230072969 + 3 ^ 40 * 835674 * 2
def baseEnd_835674 : Nat := 143034144155156218443937

theorem tailTrace_835674 : CollatzResearch.WordTrace tailWord_835674 prefixEnd_835674 143034144155156218443937 := by
  unfold tailWord_835674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7619883693625823650412519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20319689849668863067766717 7619883693625823650412519)
  ·
    refine ⟨11429825540438735475618779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7619883693625823650412519 11429825540438735475618779)
    ·
      refine ⟨17144738310658103213428169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11429825540438735475618779 17144738310658103213428169)
      ·
        refine ⟨12858553732993577410071127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17144738310658103213428169 12858553732993577410071127)
        ·
          refine ⟨19287830599490366115106691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12858553732993577410071127 19287830599490366115106691)
          ·
            refine ⟨28931745899235549172660037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19287830599490366115106691 28931745899235549172660037)
            ·
              refine ⟨5424702356106665469873757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28931745899235549172660037 5424702356106665469873757)
              ·
                refine ⟨2034263383539999551202659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5424702356106665469873757 2034263383539999551202659)
                ·
                  refine ⟨3051395075309999326803989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034263383539999551202659 3051395075309999326803989)
                  ·
                    refine ⟨143034144155156218443937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3051395075309999326803989 143034144155156218443937)
                    ·
                      rfl

theorem cell23_835674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_835674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835674 prefixEnd_835674 := by exact prefixLift 835674
  have htrace : WordTrace (prefixWord ++ tailWord_835674) baseStart_835674 baseEnd_835674 := by
    simpa [prefixWord, tailWord_835674, baseEnd_835674] using wordTrace_append hprefix tailTrace_835674
  have hstable : (prefixWord ++ tailWord_835674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835674).length < 2 ^ (prefixWord ++ tailWord_835674).sum := by decide
  have hdescent : baseEnd_835674 < baseStart_835674 := by decide
  rcases family_descends (prefixWord ++ tailWord_835674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835684 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_835684 : Nat := 118140960795 + 835684 * 2 ^ 59
def prefixEnd_835684 : Nat := 4983230072969 + 3 ^ 40 * 835684 * 2
def baseEnd_835684 : Nat := 429107567272013616206765

theorem tailTrace_835684 : CollatzResearch.WordTrace tailWord_835684 prefixEnd_835684 429107567272013616206765 := by
  unfold tailWord_835684
  simp only [CollatzResearch.WordTrace]
  refine ⟨15239949752233533154757053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20319933002978044206342737 15239949752233533154757053)
  ·
    refine ⟨5714981157087574933033895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15239949752233533154757053 5714981157087574933033895)
    ·
      refine ⟨8572471735631362399550843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5714981157087574933033895 8572471735631362399550843)
      ·
        refine ⟨12858707603447043599326265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8572471735631362399550843 12858707603447043599326265)
        ·
          refine ⟨9644030702585282699494699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12858707603447043599326265 9644030702585282699494699)
          ·
            refine ⟨14466046053877924049242049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9644030702585282699494699 14466046053877924049242049)
            ·
              refine ⟨10849534540408443036931537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14466046053877924049242049 10849534540408443036931537)
              ·
                refine ⟨8137150905306332277698653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10849534540408443036931537 8137150905306332277698653)
                ·
                  refine ⟨3051431589489874604136995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8137150905306332277698653 3051431589489874604136995)
                  ·
                    refine ⟨4577147384234811906205493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3051431589489874604136995 4577147384234811906205493)
                    ·
                      refine ⟨429107567272013616206765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4577147384234811906205493 429107567272013616206765)
                      ·
                        rfl

theorem cell23_835684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_835684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835684 prefixEnd_835684 := by exact prefixLift 835684
  have htrace : WordTrace (prefixWord ++ tailWord_835684) baseStart_835684 baseEnd_835684 := by
    simpa [prefixWord, tailWord_835684, baseEnd_835684] using wordTrace_append hprefix tailTrace_835684
  have hstable : (prefixWord ++ tailWord_835684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835684).length < 2 ^ (prefixWord ++ tailWord_835684).sum := by decide
  have hdescent : baseEnd_835684 < baseStart_835684 := by decide
  rcases family_descends (prefixWord ++ tailWord_835684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835708 : List Nat := [2, 2, 2, 1, 1, 5, 2, 2, 2, 4]
def baseStart_835708 : Nat := 118140960795 + 835708 * 2 ^ 59
def prefixEnd_835708 : Nat := 4983230072969 + 3 ^ 40 * 835708 * 2
def baseEnd_835708 : Nat := 143039963602573840768885

theorem tailTrace_835708 : CollatzResearch.WordTrace tailWord_835708 prefixEnd_835708 143039963602573840768885 := by
  unfold tailWord_835708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15240387428190059204193889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20320516570920078938925185 15240387428190059204193889)
  ·
    refine ⟨11430290571142544403145417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15240387428190059204193889 11430290571142544403145417)
    ·
      refine ⟨8572717928356908302359063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11430290571142544403145417 8572717928356908302359063)
      ·
        refine ⟨12859076892535362453538595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8572717928356908302359063 12859076892535362453538595)
        ·
          refine ⟨19288615338803043680307893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12859076892535362453538595 19288615338803043680307893)
          ·
            refine ⟨1808307688012785345028865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19288615338803043680307893 1808307688012785345028865)
            ·
              refine ⟨1356230766009589008771649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1808307688012785345028865 1356230766009589008771649)
              ·
                refine ⟨1017173074507191756578737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356230766009589008771649 1017173074507191756578737)
                ·
                  refine ⟨762879805880393817434053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1017173074507191756578737 762879805880393817434053)
                  ·
                    refine ⟨143039963602573840768885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 762879805880393817434053 143039963602573840768885)
                    ·
                      rfl

theorem cell23_835708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_835708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835708 prefixEnd_835708 := by exact prefixLift 835708
  have htrace : WordTrace (prefixWord ++ tailWord_835708) baseStart_835708 baseEnd_835708 := by
    simpa [prefixWord, tailWord_835708, baseEnd_835708] using wordTrace_append hprefix tailTrace_835708
  have hstable : (prefixWord ++ tailWord_835708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835708).length < 2 ^ (prefixWord ++ tailWord_835708).sum := by decide
  have hdescent : baseEnd_835708 < baseStart_835708 := by decide
  rcases family_descends (prefixWord ++ tailWord_835708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835731 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 6, 1, 3]
def baseStart_835731 : Nat := 118140960795 + 835731 * 2 ^ 59
def prefixEnd_835731 : Nat := 4983230072969 + 3 ^ 40 * 835731 * 2
def baseEnd_835731 : Nat := 429131700862774932319049

theorem tailTrace_835731 : CollatzResearch.WordTrace tailWord_835731 prefixEnd_835731 429131700862774932319049 := by
  unfold tailWord_835731
  simp only [CollatzResearch.WordTrace]
  refine ⟨30481613735296793336475047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20321075823531195557650031 30481613735296793336475047)
  ·
    refine ⟨45722420602945190004712571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30481613735296793336475047 45722420602945190004712571)
    ·
      refine ⟨68583630904417785007068857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45722420602945190004712571 68583630904417785007068857)
      ·
        refine ⟨51437723178313338755301643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68583630904417785007068857 51437723178313338755301643)
        ·
          refine ⟨77156584767470008132952465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51437723178313338755301643 77156584767470008132952465)
          ·
            refine ⟨57867438575602506099714349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77156584767470008132952465 57867438575602506099714349)
            ·
              refine ⟨21700289465850939787392881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57867438575602506099714349 21700289465850939787392881)
              ·
                refine ⟨16275217099388204840544661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21700289465850939787392881 16275217099388204840544661)
                ·
                  refine ⟨762900801533822101900531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16275217099388204840544661 762900801533822101900531)
                  ·
                    refine ⟨1144351202300733152850797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 762900801533822101900531 1144351202300733152850797)
                    ·
                      refine ⟨429131700862774932319049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1144351202300733152850797 429131700862774932319049)
                      ·
                        rfl

theorem cell23_835731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 6, 1, 3].length) (baseStart_835731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835731 prefixEnd_835731 := by exact prefixLift 835731
  have htrace : WordTrace (prefixWord ++ tailWord_835731) baseStart_835731 baseEnd_835731 := by
    simpa [prefixWord, tailWord_835731, baseEnd_835731] using wordTrace_append hprefix tailTrace_835731
  have hstable : (prefixWord ++ tailWord_835731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835731).length < 2 ^ (prefixWord ++ tailWord_835731).sum := by decide
  have hdescent : baseEnd_835731 < baseStart_835731 := by decide
  rcases family_descends (prefixWord ++ tailWord_835731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835738 : List Nat := [3, 1, 1, 5, 2, 1, 3, 7]
def baseStart_835738 : Nat := 118140960795 + 835738 * 2 ^ 59
def prefixEnd_835738 : Nat := 4983230072969 + 3 ^ 40 * 835738 * 2
def baseEnd_835738 : Nat := 15893899823235422404871

theorem tailTrace_835738 : CollatzResearch.WordTrace tailWord_835738 prefixEnd_835738 15893899823235422404871 := by
  unfold tailWord_835738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7620467261567858382994967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20321246030847622354653245 7620467261567858382994967)
  ·
    refine ⟨11430700892351787574492451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7620467261567858382994967 11430700892351787574492451)
    ·
      refine ⟨17146051338527681361738677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11430700892351787574492451 17146051338527681361738677)
      ·
        refine ⟨1607442312986970127663001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17146051338527681361738677 1607442312986970127663001)
        ·
          refine ⟨1205581734740227595747251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1607442312986970127663001 1205581734740227595747251)
          ·
            refine ⟨1808372602110341393620877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205581734740227595747251 1808372602110341393620877)
            ·
              refine ⟨678139725791378022607829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1808372602110341393620877 678139725791378022607829)
              ·
                refine ⟨15893899823235422404871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 678139725791378022607829 15893899823235422404871)
                ·
                  rfl

theorem cell23_835738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 3, 7].length) (baseStart_835738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835738 prefixEnd_835738 := by exact prefixLift 835738
  have htrace : WordTrace (prefixWord ++ tailWord_835738) baseStart_835738 baseEnd_835738 := by
    simpa [prefixWord, tailWord_835738, baseEnd_835738] using wordTrace_append hprefix tailTrace_835738
  have hstable : (prefixWord ++ tailWord_835738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835738).length < 2 ^ (prefixWord ++ tailWord_835738).sum := by decide
  have hdescent : baseEnd_835738 < baseStart_835738 := by decide
  rcases family_descends (prefixWord ++ tailWord_835738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835838 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_835838 : Nat := 118140960795 + 835838 * 2 ^ 59
def prefixEnd_835838 : Nat := 4983230072969 + 3 ^ 40 * 835838 * 2
def baseEnd_835838 : Nat := 429186643292806013681057

theorem tailTrace_835838 : CollatzResearch.WordTrace tailWord_835838 prefixEnd_835838 429186643292806013681057 := by
  unfold tailWord_835838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3810689543238643826327521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20323677563939433740413445 3810689543238643826327521)
  ·
    refine ⟨2858017157428982869745641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3810689543238643826327521 2858017157428982869745641)
    ·
      refine ⟨2143512868071737152309231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2858017157428982869745641 2143512868071737152309231)
      ·
        refine ⟨3215269302107605728463847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2143512868071737152309231 3215269302107605728463847)
        ·
          refine ⟨4822903953161408592695771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3215269302107605728463847 4822903953161408592695771)
          ·
            refine ⟨7234355929742112889043657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822903953161408592695771 7234355929742112889043657)
            ·
              refine ⟨5425766947306584666782743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7234355929742112889043657 5425766947306584666782743)
              ·
                refine ⟨8138650420959877000174115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5425766947306584666782743 8138650420959877000174115)
                ·
                  refine ⟨12207975631439815500261173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8138650420959877000174115 12207975631439815500261173)
                  ·
                    refine ⟨1144497715447482703149485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12207975631439815500261173 1144497715447482703149485)
                    ·
                      refine ⟨429186643292806013681057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1144497715447482703149485 429186643292806013681057)
                      ·
                        rfl

theorem cell23_835838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_835838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835838 prefixEnd_835838 := by exact prefixLift 835838
  have htrace : WordTrace (prefixWord ++ tailWord_835838) baseStart_835838 baseEnd_835838 := by
    simpa [prefixWord, tailWord_835838, baseEnd_835838] using wordTrace_append hprefix tailTrace_835838
  have hstable : (prefixWord ++ tailWord_835838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835838).length < 2 ^ (prefixWord ++ tailWord_835838).sum := by decide
  have hdescent : baseEnd_835838 < baseStart_835838 := by decide
  rcases family_descends (prefixWord ++ tailWord_835838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835841 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 4, 5]
def baseStart_835841 : Nat := 118140960795 + 835841 * 2 ^ 59
def prefixEnd_835841 : Nat := 4983230072969 + 3 ^ 40 * 835841 * 2
def baseEnd_835841 : Nat := 143062727911589833981181

theorem tailTrace_835841 : CollatzResearch.WordTrace tailWord_835841 prefixEnd_835841 143062727911589833981181 := by
  unfold tailWord_835841
  simp only [CollatzResearch.WordTrace]
  refine ⟨30485625764898282122979377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20323750509932188081986251 30485625764898282122979377)
  ·
    refine ⟨22864219323673711592234533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30485625764898282122979377 22864219323673711592234533)
    ·
      refine ⟨4287041123188820923543975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22864219323673711592234533 4287041123188820923543975)
      ·
        refine ⟨6430561684783231385315963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4287041123188820923543975 6430561684783231385315963)
        ·
          refine ⟨9645842527174847077973945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6430561684783231385315963 9645842527174847077973945)
          ·
            refine ⟨7234381895381135308480459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9645842527174847077973945 7234381895381135308480459)
            ·
              refine ⟨10851572843071702962720689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7234381895381135308480459 10851572843071702962720689)
              ·
                refine ⟨8138679632303777222040517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10851572843071702962720689 8138679632303777222040517)
                ·
                  refine ⟨1526002431056958229132597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8138679632303777222040517 1526002431056958229132597)
                  ·
                    refine ⟨143062727911589833981181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1526002431056958229132597 143062727911589833981181)
                    ·
                      rfl

theorem cell23_835841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_835841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835841 prefixEnd_835841 := by exact prefixLift 835841
  have htrace : WordTrace (prefixWord ++ tailWord_835841) baseStart_835841 baseEnd_835841 := by
    simpa [prefixWord, tailWord_835841, baseEnd_835841] using wordTrace_append hprefix tailTrace_835841
  have hstable : (prefixWord ++ tailWord_835841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835841).length < 2 ^ (prefixWord ++ tailWord_835841).sum := by decide
  have hdescent : baseEnd_835841 < baseStart_835841 := by decide
  rcases family_descends (prefixWord ++ tailWord_835841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835861 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_835861 : Nat := 118140960795 + 835861 * 2 ^ 59
def prefixEnd_835861 : Nat := 4983230072969 + 3 ^ 40 * 835861 * 2
def baseEnd_835861 : Nat := 429198453347859423693451

theorem tailTrace_835861 : CollatzResearch.WordTrace tailWord_835861 prefixEnd_835861 429198453347859423693451 := by
  unfold tailWord_835861
  simp only [CollatzResearch.WordTrace]
  refine ⟨30486355224825825538707437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20324236816550550359138291 30486355224825825538707437)
  ·
    refine ⟨11432383209309684577015289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30486355224825825538707437 11432383209309684577015289)
    ·
      refine ⟨8574287406982263432761467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11432383209309684577015289 8574287406982263432761467)
      ·
        refine ⟨12861431110473395149142201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8574287406982263432761467 12861431110473395149142201)
        ·
          refine ⟨9646073332855046361856651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12861431110473395149142201 9646073332855046361856651)
          ·
            refine ⟨14469109999282569542784977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9646073332855046361856651 14469109999282569542784977)
            ·
              refine ⟨10851832499461927157088733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14469109999282569542784977 10851832499461927157088733)
              ·
                refine ⟨4069437187298222683908275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10851832499461927157088733 4069437187298222683908275)
                ·
                  refine ⟨6104155780947334025862413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4069437187298222683908275 6104155780947334025862413)
                  ·
                    refine ⟨2289058417855250259698405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6104155780947334025862413 2289058417855250259698405)
                    ·
                      refine ⟨429198453347859423693451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2289058417855250259698405 429198453347859423693451)
                      ·
                        rfl

theorem cell23_835861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_835861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835861 prefixEnd_835861 := by exact prefixLift 835861
  have htrace : WordTrace (prefixWord ++ tailWord_835861) baseStart_835861 baseEnd_835861 := by
    simpa [prefixWord, tailWord_835861, baseEnd_835861] using wordTrace_append hprefix tailTrace_835861
  have hstable : (prefixWord ++ tailWord_835861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835861).length < 2 ^ (prefixWord ++ tailWord_835861).sum := by decide
  have hdescent : baseEnd_835861 < baseStart_835861 := by decide
  rcases family_descends (prefixWord ++ tailWord_835861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835879 : List Nat := [1, 1, 8, 1, 1, 1, 1, 4, 5]
def baseStart_835879 : Nat := 118140960795 + 835879 * 2 ^ 59
def prefixEnd_835879 : Nat := 4983230072969 + 3 ^ 40 * 835879 * 2
def baseEnd_835879 : Nat := 47689743999960039252041

theorem tailTrace_835879 : CollatzResearch.WordTrace tailWord_835879 prefixEnd_835879 47689743999960039252041 := by
  unfold tailWord_835879
  simp only [CollatzResearch.WordTrace]
  refine ⟨30487011738760614612862691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20324674492507076408575127 30487011738760614612862691)
  ·
    refine ⟨45730517608140921919294037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30487011738760614612862691 45730517608140921919294037)
    ·
      refine ⟨535904503220401428741727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 45730517608140921919294037 535904503220401428741727)
      ·
        refine ⟨803856754830602143112591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535904503220401428741727 803856754830602143112591)
        ·
          refine ⟨1205785132245903214668887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803856754830602143112591 1205785132245903214668887)
          ·
            refine ⟨1808677698368854822003331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205785132245903214668887 1808677698368854822003331)
            ·
              refine ⟨2713016547553282233004997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1808677698368854822003331 2713016547553282233004997)
              ·
                refine ⟨508690602666240418688437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2713016547553282233004997 508690602666240418688437)
                ·
                  refine ⟨47689743999960039252041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 508690602666240418688437 47689743999960039252041)
                  ·
                    rfl

theorem cell23_835879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 4, 5].length) (baseStart_835879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835879 prefixEnd_835879 := by exact prefixLift 835879
  have htrace : WordTrace (prefixWord ++ tailWord_835879) baseStart_835879 baseEnd_835879 := by
    simpa [prefixWord, tailWord_835879, baseEnd_835879] using wordTrace_append hprefix tailTrace_835879
  have hstable : (prefixWord ++ tailWord_835879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835879).length < 2 ^ (prefixWord ++ tailWord_835879).sum := by decide
  have hdescent : baseEnd_835879 < baseStart_835879 := by decide
  rcases family_descends (prefixWord ++ tailWord_835879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835938 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_835938 : Nat := 118140960795 + 835938 * 2 ^ 59
def prefixEnd_835938 : Nat := 4983230072969 + 3 ^ 40 * 835938 * 2
def baseEnd_835938 : Nat := 429237991358255622430597

theorem tailTrace_835938 : CollatzResearch.WordTrace tailWord_835938 prefixEnd_835938 429237991358255622430597 := by
  unfold tailWord_835938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7622290911386716922315117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20326109097031245126173645 7622290911386716922315117)
  ·
    refine ⟨2858359091770018845868169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7622290911386716922315117 2858359091770018845868169)
    ·
      refine ⟨2143769318827514134401127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2858359091770018845868169 2143769318827514134401127)
      ·
        refine ⟨3215653978241271201601691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2143769318827514134401127 3215653978241271201601691)
        ·
          refine ⟨4823480967361906802402537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3215653978241271201601691 4823480967361906802402537)
          ·
            refine ⟨3617610725521430101801903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4823480967361906802402537 3617610725521430101801903)
            ·
              refine ⟨5426416088282145152702855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3617610725521430101801903 5426416088282145152702855)
              ·
                refine ⟨8139624132423217729054283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5426416088282145152702855 8139624132423217729054283)
                ·
                  refine ⟨12209436198634826593581425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8139624132423217729054283 12209436198634826593581425)
                  ·
                    refine ⟨9157077148976119945186069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12209436198634826593581425 9157077148976119945186069)
                    ·
                      refine ⟨429237991358255622430597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9157077148976119945186069 429237991358255622430597)
                      ·
                        rfl

theorem cell23_835938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_835938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835938 prefixEnd_835938 := by exact prefixLift 835938
  have htrace : WordTrace (prefixWord ++ tailWord_835938) baseStart_835938 baseEnd_835938 := by
    simpa [prefixWord, tailWord_835938, baseEnd_835938] using wordTrace_append hprefix tailTrace_835938
  have hstable : (prefixWord ++ tailWord_835938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835938).length < 2 ^ (prefixWord ++ tailWord_835938).sum := by decide
  have hdescent : baseEnd_835938 < baseStart_835938 := by decide
  rcases family_descends (prefixWord ++ tailWord_835938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835945 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 3, 1, 3]
def baseStart_835945 : Nat := 118140960795 + 835945 * 2 ^ 59
def prefixEnd_835945 : Nat := 4983230072969 + 3 ^ 40 * 835945 * 2
def baseEnd_835945 : Nat := 429241585722837095043065

theorem tailTrace_835945 : CollatzResearch.WordTrace tailWord_835945 prefixEnd_835945 429241585722837095043065 := by
  unfold tailWord_835945
  simp only [CollatzResearch.WordTrace]
  refine ⟨30489418956521507884765289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20326279304347671923176859 30489418956521507884765289)
  ·
    refine ⟨22867064217391130913573967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30489418956521507884765289 22867064217391130913573967)
    ·
      refine ⟨34300596326086696370360951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22867064217391130913573967 34300596326086696370360951)
      ·
        refine ⟨51450894489130044555541427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34300596326086696370360951 51450894489130044555541427)
        ·
          refine ⟨77176341733695066833312141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51450894489130044555541427 77176341733695066833312141)
          ·
            refine ⟨28941128150135650062492053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77176341733695066833312141 28941128150135650062492053)
            ·
              refine ⟨1356615382037608596679315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28941128150135650062492053 1356615382037608596679315)
              ·
                refine ⟨2034923073056412895018973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1356615382037608596679315 2034923073056412895018973)
                ·
                  refine ⟨763096152396154835632115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2034923073056412895018973 763096152396154835632115)
                  ·
                    refine ⟨1144644228594232253448173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 763096152396154835632115 1144644228594232253448173)
                    ·
                      refine ⟨429241585722837095043065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1144644228594232253448173 429241585722837095043065)
                      ·
                        rfl

theorem cell23_835945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 3, 1, 3].length) (baseStart_835945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835945 prefixEnd_835945 := by exact prefixLift 835945
  have htrace : WordTrace (prefixWord ++ tailWord_835945) baseStart_835945 baseEnd_835945 := by
    simpa [prefixWord, tailWord_835945, baseEnd_835945] using wordTrace_append hprefix tailTrace_835945
  have hstable : (prefixWord ++ tailWord_835945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835945).length < 2 ^ (prefixWord ++ tailWord_835945).sum := by decide
  have hdescent : baseEnd_835945 < baseStart_835945 := by decide
  rcases family_descends (prefixWord ++ tailWord_835945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835951 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 4]
def baseStart_835951 : Nat := 118140960795 + 835951 * 2 ^ 59
def prefixEnd_835951 : Nat := 4983230072969 + 3 ^ 40 * 835951 * 2
def baseEnd_835951 : Nat := 429244666606764071568037

theorem tailTrace_835951 : CollatzResearch.WordTrace tailWord_835951 prefixEnd_835951 429244666606764071568037 := by
  unfold tailWord_835951
  simp only [CollatzResearch.WordTrace]
  refine ⟨30489637794499770909483707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20326425196333180606322471 30489637794499770909483707)
  ·
    refine ⟨45734456691749656364225561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30489637794499770909483707 45734456691749656364225561)
    ·
      refine ⟨34300842518812242273169171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45734456691749656364225561 34300842518812242273169171)
      ·
        refine ⟨51451263778218363409753757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34300842518812242273169171 51451263778218363409753757)
        ·
          refine ⟨19294223916831886278657659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51451263778218363409753757 19294223916831886278657659)
          ·
            refine ⟨28941335875247829417986489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19294223916831886278657659 28941335875247829417986489)
            ·
              refine ⟨21706001906435872063489867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28941335875247829417986489 21706001906435872063489867)
              ·
                refine ⟨32559002859653808095234801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21706001906435872063489867 32559002859653808095234801)
                ·
                  refine ⟨24419252144740356071426101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32559002859653808095234801 24419252144740356071426101)
                  ·
                    refine ⟨2289304888569408381696197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24419252144740356071426101 2289304888569408381696197)
                    ·
                      refine ⟨429244666606764071568037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2289304888569408381696197 429244666606764071568037)
                      ·
                        rfl

theorem cell23_835951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_835951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835951 prefixEnd_835951 := by exact prefixLift 835951
  have htrace : WordTrace (prefixWord ++ tailWord_835951) baseStart_835951 baseEnd_835951 := by
    simpa [prefixWord, tailWord_835951, baseEnd_835951] using wordTrace_append hprefix tailTrace_835951
  have hstable : (prefixWord ++ tailWord_835951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835951).length < 2 ^ (prefixWord ++ tailWord_835951).sum := by decide
  have hdescent : baseEnd_835951 < baseStart_835951 := by decide
  rcases family_descends (prefixWord ++ tailWord_835951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835965 : List Nat := [1, 4, 1, 1, 2, 4, 2, 2, 1, 5]
def baseStart_835965 : Nat := 118140960795 + 835965 * 2 ^ 59
def prefixEnd_835965 : Nat := 4983230072969 + 3 ^ 40 * 835965 * 2
def baseEnd_835965 : Nat := 143083951778642338930991

theorem tailTrace_835965 : CollatzResearch.WordTrace tailWord_835965 prefixEnd_835965 143083951778642338930991 := by
  unfold tailWord_835965
  simp only [CollatzResearch.WordTrace]
  refine ⟨30490148416449051300493349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20326765610966034200328899 30490148416449051300493349)
  ·
    refine ⟨5716902828084197118842503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30490148416449051300493349 5716902828084197118842503)
    ·
      refine ⟨8575354242126295678263755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5716902828084197118842503 8575354242126295678263755)
      ·
        refine ⟨12863031363189443517395633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8575354242126295678263755 12863031363189443517395633)
        ·
          refine ⟨9647273522392082638046725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12863031363189443517395633 9647273522392082638046725)
          ·
            refine ⟨1808863785448515494633761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9647273522392082638046725 1808863785448515494633761)
            ·
              refine ⟨1356647839086386620975321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1808863785448515494633761 1356647839086386620975321)
              ·
                refine ⟨1017485879314789965731491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356647839086386620975321 1017485879314789965731491)
                ·
                  refine ⟨1526228818972184948597237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017485879314789965731491 1526228818972184948597237)
                  ·
                    refine ⟨143083951778642338930991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1526228818972184948597237 143083951778642338930991)
                    ·
                      rfl

theorem cell23_835965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_835965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835965 prefixEnd_835965 := by exact prefixLift 835965
  have htrace : WordTrace (prefixWord ++ tailWord_835965) baseStart_835965 baseEnd_835965 := by
    simpa [prefixWord, tailWord_835965, baseEnd_835965] using wordTrace_append hprefix tailTrace_835965
  have hstable : (prefixWord ++ tailWord_835965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835965).length < 2 ^ (prefixWord ++ tailWord_835965).sum := by decide
  have hdescent : baseEnd_835965 < baseStart_835965 := by decide
  rcases family_descends (prefixWord ++ tailWord_835965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835979 : List Nat := [1, 1, 1, 1, 4, 6, 1, 3, 1, 1, 3]
def baseStart_835979 : Nat := 118140960795 + 835979 * 2 ^ 59
def prefixEnd_835979 : Nat := 4983230072969 + 3 ^ 40 * 835979 * 2
def baseEnd_835979 : Nat := 429259044065089962017909

theorem tailTrace_835979 : CollatzResearch.WordTrace tailWord_835979 prefixEnd_835979 429259044065089962017909 := by
  unfold tailWord_835979
  simp only [CollatzResearch.WordTrace]
  refine ⟨30490659038398331691502991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20327106025598887794335327 30490659038398331691502991)
  ·
    refine ⟨45735988557597497537254487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30490659038398331691502991 45735988557597497537254487)
    ·
      refine ⟨68603982836396246305881731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45735988557597497537254487 68603982836396246305881731)
      ·
        refine ⟨102905974254594369458822597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68603982836396246305881731 102905974254594369458822597)
        ·
          refine ⟨19294870172736444273529237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102905974254594369458822597 19294870172736444273529237)
          ·
            refine ⟨904447039347020825321683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19294870172736444273529237 904447039347020825321683)
            ·
              refine ⟨1356670559020531237982525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904447039347020825321683 1356670559020531237982525)
              ·
                refine ⟨508751459632699214243447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1356670559020531237982525 508751459632699214243447)
                ·
                  refine ⟨763127189449048821365171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508751459632699214243447 763127189449048821365171)
                  ·
                    refine ⟨1144690784173573232047757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 763127189449048821365171 1144690784173573232047757)
                    ·
                      refine ⟨429259044065089962017909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1144690784173573232047757 429259044065089962017909)
                      ·
                        rfl

theorem cell23_835979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 1, 1, 3].length) (baseStart_835979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835979 prefixEnd_835979 := by exact prefixLift 835979
  have htrace : WordTrace (prefixWord ++ tailWord_835979) baseStart_835979 baseEnd_835979 := by
    simpa [prefixWord, tailWord_835979, baseEnd_835979] using wordTrace_append hprefix tailTrace_835979
  have hstable : (prefixWord ++ tailWord_835979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835979).length < 2 ^ (prefixWord ++ tailWord_835979).sum := by decide
  have hdescent : baseEnd_835979 < baseStart_835979 := by decide
  rcases family_descends (prefixWord ++ tailWord_835979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835990 : List Nat := [5, 3, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_835990 : Nat := 118140960795 + 835990 * 2 ^ 59
def prefixEnd_835990 : Nat := 4983230072969 + 3 ^ 40 * 835990 * 2
def baseEnd_835990 : Nat := 143088230784096472993453

theorem tailTrace_835990 : CollatzResearch.WordTrace tailWord_835990 prefixEnd_835990 143088230784096472993453 := by
  unfold tailWord_835990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905691265084905035634589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20327373494238987046768949 1905691265084905035634589)
  ·
    refine ⟨714634224406839388362971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1905691265084905035634589 714634224406839388362971)
    ·
      refine ⟨1071951336610259082544457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 714634224406839388362971 1071951336610259082544457)
      ·
        refine ⟨803963502457694311908343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1071951336610259082544457 803963502457694311908343)
        ·
          refine ⟨1205945253686541467862515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803963502457694311908343 1205945253686541467862515)
          ·
            refine ⟨1808917880529812201793773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205945253686541467862515 1808917880529812201793773)
            ·
              refine ⟨678344205198679575672665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1808917880529812201793773 678344205198679575672665)
              ·
                refine ⟨508758153899009681754499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678344205198679575672665 508758153899009681754499)
                ·
                  refine ⟨763137230848514522631749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508758153899009681754499 763137230848514522631749)
                  ·
                    refine ⟨143088230784096472993453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 763137230848514522631749 143088230784096472993453)
                    ·
                      rfl

theorem cell23_835990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_835990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835990 prefixEnd_835990 := by exact prefixLift 835990
  have htrace : WordTrace (prefixWord ++ tailWord_835990) baseStart_835990 baseEnd_835990 := by
    simpa [prefixWord, tailWord_835990, baseEnd_835990] using wordTrace_append hprefix tailTrace_835990
  have hstable : (prefixWord ++ tailWord_835990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835990).length < 2 ^ (prefixWord ++ tailWord_835990).sum := by decide
  have hdescent : baseEnd_835990 < baseStart_835990 := by decide
  rcases family_descends (prefixWord ++ tailWord_835990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835991 : List Nat := [1, 1, 3, 3, 1, 1, 13]
def baseStart_835991 : Nat := 118140960795 + 835991 * 2 ^ 59
def prefixEnd_835991 : Nat := 4983230072969 + 3 ^ 40 * 835991 * 2
def baseEnd_835991 : Nat := 5299570442382023642813

theorem tailTrace_835991 : CollatzResearch.WordTrace tailWord_835991 prefixEnd_835991 5299570442382023642813 := by
  unfold tailWord_835991
  simp only [CollatzResearch.WordTrace]
  refine ⟨30491096714354857740939827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20327397809569905160626551 30491096714354857740939827)
  ·
    refine ⟨45736645071532286611409741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30491096714354857740939827 45736645071532286611409741)
    ·
      refine ⟨17151241901824607479278653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45736645071532286611409741 17151241901824607479278653)
      ·
        refine ⟨6431715713184227804729495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17151241901824607479278653 6431715713184227804729495)
        ·
          refine ⟨9647573569776341707094243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6431715713184227804729495 9647573569776341707094243)
          ·
            refine ⟨14471360354664512560641365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9647573569776341707094243 14471360354664512560641365)
            ·
              refine ⟨5299570442382023642813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 14471360354664512560641365 5299570442382023642813)
              ·
                rfl

theorem cell23_835991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 13].length) (baseStart_835991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_835991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_835991 prefixEnd_835991 := by exact prefixLift 835991
  have htrace : WordTrace (prefixWord ++ tailWord_835991) baseStart_835991 baseEnd_835991 := by
    simpa [prefixWord, tailWord_835991, baseEnd_835991] using wordTrace_append hprefix tailTrace_835991
  have hstable : (prefixWord ++ tailWord_835991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835991).length < 2 ^ (prefixWord ++ tailWord_835991).sum := by decide
  have hdescent : baseEnd_835991 < baseStart_835991 := by decide
  rcases family_descends (prefixWord ++ tailWord_835991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836053 : List Nat := [1, 3, 2, 3, 1, 4, 2, 2, 1, 2, 2]
def baseStart_836053 : Nat := 118140960795 + 836053 * 2 ^ 59
def prefixEnd_836053 : Nat := 4983230072969 + 3 ^ 40 * 836053 * 2
def baseEnd_836053 : Nat := 429297041633522672492569

theorem tailTrace_836053 : CollatzResearch.WordTrace tailWord_836053 prefixEnd_836053 429297041633522672492569 := by
  unfold tailWord_836053
  simp only [CollatzResearch.WordTrace]
  refine ⟨30493358040130242329696813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20328905360086828219797875 30493358040130242329696813)
  ·
    refine ⟨11435009265048840873636305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30493358040130242329696813 11435009265048840873636305)
    ·
      refine ⟨8576256948786630655227229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11435009265048840873636305 8576256948786630655227229)
      ·
        refine ⟨3216096355794986495710211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8576256948786630655227229 3216096355794986495710211)
        ·
          refine ⟨4824144533692479743565317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3216096355794986495710211 4824144533692479743565317)
          ·
            refine ⟨904527100067339951918497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4824144533692479743565317 904527100067339951918497)
            ·
              refine ⟨678395325050504963938873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 904527100067339951918497 678395325050504963938873)
              ·
                refine ⟨508796493787878722954155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678395325050504963938873 508796493787878722954155)
                ·
                  refine ⟨763194740681818084431233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508796493787878722954155 763194740681818084431233)
                  ·
                    refine ⟨572396055511363563323425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 763194740681818084431233 572396055511363563323425)
                    ·
                      refine ⟨429297041633522672492569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 572396055511363563323425 429297041633522672492569)
                      ·
                        rfl

theorem cell23_836053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_836053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836053 prefixEnd_836053 := by exact prefixLift 836053
  have htrace : WordTrace (prefixWord ++ tailWord_836053) baseStart_836053 baseEnd_836053 := by
    simpa [prefixWord, tailWord_836053, baseEnd_836053] using wordTrace_append hprefix tailTrace_836053
  have hstable : (prefixWord ++ tailWord_836053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836053).length < 2 ^ (prefixWord ++ tailWord_836053).sum := by decide
  have hdescent : baseEnd_836053 < baseStart_836053 := by decide
  rcases family_descends (prefixWord ++ tailWord_836053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836058 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_836058 : Nat := 118140960795 + 836058 * 2 ^ 59
def prefixEnd_836058 : Nat := 4983230072969 + 3 ^ 40 * 836058 * 2
def baseEnd_836058 : Nat := 429299609036795152930045

theorem tailTrace_836058 : CollatzResearch.WordTrace tailWord_836058 prefixEnd_836058 429299609036795152930045 := by
  unfold tailWord_836058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7623385101278032045907207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20329026936741418789085885 7623385101278032045907207)
  ·
    refine ⟨11435077651917048068860811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7623385101278032045907207 11435077651917048068860811)
    ·
      refine ⟨17152616477875572103291217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11435077651917048068860811 17152616477875572103291217)
      ·
        refine ⟨12864462358406679077468413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17152616477875572103291217 12864462358406679077468413)
        ·
          refine ⟨4824173384402504654050655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12864462358406679077468413 4824173384402504654050655)
          ·
            refine ⟨7236260076603756981075983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824173384402504654050655 7236260076603756981075983)
            ·
              refine ⟨10854390114905635471613975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236260076603756981075983 10854390114905635471613975)
              ·
                refine ⟨16281585172358453207420963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10854390114905635471613975 16281585172358453207420963)
                ·
                  refine ⟨24422377758537679811131445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16281585172358453207420963 24422377758537679811131445)
                  ·
                    refine ⟨2289597914862907482293573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24422377758537679811131445 2289597914862907482293573)
                    ·
                      refine ⟨429299609036795152930045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2289597914862907482293573 429299609036795152930045)
                      ·
                        rfl

theorem cell23_836058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_836058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836058 prefixEnd_836058 := by exact prefixLift 836058
  have htrace : WordTrace (prefixWord ++ tailWord_836058) baseStart_836058 baseEnd_836058 := by
    simpa [prefixWord, tailWord_836058, baseEnd_836058] using wordTrace_append hprefix tailTrace_836058
  have hstable : (prefixWord ++ tailWord_836058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836058).length < 2 ^ (prefixWord ++ tailWord_836058).sum := by decide
  have hdescent : baseEnd_836058 < baseStart_836058 := by decide
  rcases family_descends (prefixWord ++ tailWord_836058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836088 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_836088 : Nat := 118140960795 + 836088 * 2 ^ 59
def prefixEnd_836088 : Nat := 4983230072969 + 3 ^ 40 * 836088 * 2
def baseEnd_836088 : Nat := 429315013456430035554907

theorem tailTrace_836088 : CollatzResearch.WordTrace tailWord_836088 prefixEnd_836088 429315013456430035554907 := by
  unfold tailWord_836088
  simp only [CollatzResearch.WordTrace]
  refine ⟨15247317297501721653610459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20329756396668962204813945 15247317297501721653610459)
  ·
    refine ⟨22870975946252582480415689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15247317297501721653610459 22870975946252582480415689)
    ·
      refine ⟨17153231959689436860311767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22870975946252582480415689 17153231959689436860311767)
      ·
        refine ⟨25729847939534155290467651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17153231959689436860311767 25729847939534155290467651)
        ·
          refine ⟨38594771909301232935701477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25729847939534155290467651 38594771909301232935701477)
          ·
            refine ⟨7236519732993981175444027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38594771909301232935701477 7236519732993981175444027)
            ·
              refine ⟨10854779599490971763166041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236519732993981175444027 10854779599490971763166041)
              ·
                refine ⟨8141084699618228822374531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10854779599490971763166041 8141084699618228822374531)
                ·
                  refine ⟨12211627049427343233561797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8141084699618228822374531 12211627049427343233561797)
                  ·
                    refine ⟨2289680071767626856292837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12211627049427343233561797 2289680071767626856292837)
                    ·
                      refine ⟨429315013456430035554907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2289680071767626856292837 429315013456430035554907)
                      ·
                        rfl

theorem cell23_836088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_836088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836088 prefixEnd_836088 := by exact prefixLift 836088
  have htrace : WordTrace (prefixWord ++ tailWord_836088) baseStart_836088 baseEnd_836088 := by
    simpa [prefixWord, tailWord_836088, baseEnd_836088] using wordTrace_append hprefix tailTrace_836088
  have hstable : (prefixWord ++ tailWord_836088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836088).length < 2 ^ (prefixWord ++ tailWord_836088).sum := by decide
  have hdescent : baseEnd_836088 < baseStart_836088 := by decide
  rcases family_descends (prefixWord ++ tailWord_836088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836092 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 4, 2, 2]
def baseStart_836092 : Nat := 118140960795 + 836092 * 2 ^ 59
def prefixEnd_836092 : Nat := 4983230072969 + 3 ^ 40 * 836092 * 2
def baseEnd_836092 : Nat := 429317067379048019904889

theorem tailTrace_836092 : CollatzResearch.WordTrace tailWord_836092 prefixEnd_836092 429317067379048019904889 := by
  unfold tailWord_836092
  simp only [CollatzResearch.WordTrace]
  refine ⟨15247390243494475995183265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20329853657992634660244353 15247390243494475995183265)
  ·
    refine ⟨11435542682620856996387449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15247390243494475995183265 11435542682620856996387449)
    ·
      refine ⟨8576657011965642747290587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11435542682620856996387449 8576657011965642747290587)
      ·
        refine ⟨12864985517948464120935881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8576657011965642747290587 12864985517948464120935881)
        ·
          refine ⟨9648739138461348090701911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12864985517948464120935881 9648739138461348090701911)
          ·
            refine ⟨14473108707692022136052867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9648739138461348090701911 14473108707692022136052867)
            ·
              refine ⟨21709663061538033204079301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14473108707692022136052867 21709663061538033204079301)
              ·
                refine ⟨4070561824038381225764869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21709663061538033204079301 4070561824038381225764869)
                ·
                  refine ⟨763230342007196479830913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4070561824038381225764869 763230342007196479830913)
                  ·
                    refine ⟨572422756505397359873185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 763230342007196479830913 572422756505397359873185)
                    ·
                      refine ⟨429317067379048019904889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 572422756505397359873185 429317067379048019904889)
                      ·
                        rfl

theorem cell23_836092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_836092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836092 prefixEnd_836092 := by exact prefixLift 836092
  have htrace : WordTrace (prefixWord ++ tailWord_836092) baseStart_836092 baseEnd_836092 := by
    simpa [prefixWord, tailWord_836092, baseEnd_836092] using wordTrace_append hprefix tailTrace_836092
  have hstable : (prefixWord ++ tailWord_836092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836092).length < 2 ^ (prefixWord ++ tailWord_836092).sum := by decide
  have hdescent : baseEnd_836092 < baseStart_836092 := by decide
  rcases family_descends (prefixWord ++ tailWord_836092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836115 : List Nat := [1, 1, 1, 2, 1, 5, 1, 6, 5]
def baseStart_836115 : Nat := 118140960795 + 836115 * 2 ^ 59
def prefixEnd_836115 : Nat := 4983230072969 + 3 ^ 40 * 836115 * 2
def baseEnd_836115 : Nat := 47703208603789047768587

theorem tailTrace_836115 : CollatzResearch.WordTrace tailWord_836115 prefixEnd_836115 47703208603789047768587 := by
  unfold tailWord_836115
  simp only [CollatzResearch.WordTrace]
  refine ⟨30495619365905626918453799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20330412910603751278969199 30495619365905626918453799)
  ·
    refine ⟨45743429048858440377680699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30495619365905626918453799 45743429048858440377680699)
    ·
      refine ⟨68615143573287660566521049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45743429048858440377680699 68615143573287660566521049)
      ·
        refine ⟨51461357679965745424890787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68615143573287660566521049 51461357679965745424890787)
        ·
          refine ⟨77192036519948618137336181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51461357679965745424890787 77192036519948618137336181)
          ·
            refine ⟨7236753423745182950375267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77192036519948618137336181 7236753423745182950375267)
            ·
              refine ⟨10855130135617774425562901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236753423745182950375267 10855130135617774425562901)
              ·
                refine ⟨508834225107083176198261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10855130135617774425562901 508834225107083176198261)
                ·
                  refine ⟨47703208603789047768587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 508834225107083176198261 47703208603789047768587)
                  ·
                    rfl

theorem cell23_836115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 6, 5].length) (baseStart_836115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836115 prefixEnd_836115 := by exact prefixLift 836115
  have htrace : WordTrace (prefixWord ++ tailWord_836115) baseStart_836115 baseEnd_836115 := by
    simpa [prefixWord, tailWord_836115, baseEnd_836115] using wordTrace_append hprefix tailTrace_836115
  have hstable : (prefixWord ++ tailWord_836115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836115).length < 2 ^ (prefixWord ++ tailWord_836115).sum := by decide
  have hdescent : baseEnd_836115 < baseStart_836115 := by decide
  rcases family_descends (prefixWord ++ tailWord_836115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836165 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_836165 : Nat := 118140960795 + 836165 * 2 ^ 59
def prefixEnd_836165 : Nat := 4983230072969 + 3 ^ 40 * 836165 * 2
def baseEnd_836165 : Nat := 429354551466826234292053

theorem tailTrace_836165 : CollatzResearch.WordTrace tailWord_836165 prefixEnd_836165 429354551466826234292053 := by
  unfold tailWord_836165
  simp only [CollatzResearch.WordTrace]
  refine ⟨30497443015724485457773949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20331628677149656971849299 30497443015724485457773949)
  ·
    refine ⟨11436541130896682046665231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30497443015724485457773949 11436541130896682046665231)
    ·
      refine ⟨17154811696345023069997847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11436541130896682046665231 17154811696345023069997847)
      ·
        refine ⟨25732217544517534604996771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17154811696345023069997847 25732217544517534604996771)
        ·
          refine ⟨38598326316776301907495157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25732217544517534604996771 38598326316776301907495157)
          ·
            refine ⟨3618593092197778303827671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38598326316776301907495157 3618593092197778303827671)
            ·
              refine ⟨5427889638296667455741507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3618593092197778303827671 5427889638296667455741507)
              ·
                refine ⟨8141834457445001183612261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5427889638296667455741507 8141834457445001183612261)
                ·
                  refine ⟨1526593960770937721927299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8141834457445001183612261 1526593960770937721927299)
                  ·
                    refine ⟨2289890941156406582890949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1526593960770937721927299 2289890941156406582890949)
                    ·
                      refine ⟨429354551466826234292053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2289890941156406582890949 429354551466826234292053)
                      ·
                        rfl

theorem cell23_836165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_836165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836165 prefixEnd_836165 := by exact prefixLift 836165
  have htrace : WordTrace (prefixWord ++ tailWord_836165) baseStart_836165 baseEnd_836165 := by
    simpa [prefixWord, tailWord_836165, baseEnd_836165] using wordTrace_append hprefix tailTrace_836165
  have hstable : (prefixWord ++ tailWord_836165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836165).length < 2 ^ (prefixWord ++ tailWord_836165).sum := by decide
  have hdescent : baseEnd_836165 < baseStart_836165 := by decide
  rcases family_descends (prefixWord ++ tailWord_836165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836225 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_836225 : Nat := 118140960795 + 836225 * 2 ^ 59
def prefixEnd_836225 : Nat := 4983230072969 + 3 ^ 40 * 836225 * 2
def baseEnd_836225 : Nat := 429385360306095999541777

theorem tailTrace_836225 : CollatzResearch.WordTrace tailWord_836225 prefixEnd_836225 429385360306095999541777 := by
  unfold tailWord_836225
  simp only [CollatzResearch.WordTrace]
  refine ⟨30499631395507115704958129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20333087597004743803305419 30499631395507115704958129)
  ·
    refine ⟨22874723546630336778718597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30499631395507115704958129 22874723546630336778718597)
    ·
      refine ⟨4289010664993188146009737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22874723546630336778718597 4289010664993188146009737)
      ·
        refine ⟨3216757998744891109507303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4289010664993188146009737 3216757998744891109507303)
        ·
          refine ⟨4825136998117336664260955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3216757998744891109507303 4825136998117336664260955)
          ·
            refine ⟨7237705497176004996391433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4825136998117336664260955 7237705497176004996391433)
            ·
              refine ⟨5428279122882003747293575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7237705497176004996391433 5428279122882003747293575)
              ·
                refine ⟨8142418684323005620940363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5428279122882003747293575 8142418684323005620940363)
                ·
                  refine ⟨12213628026484508431410545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8142418684323005620940363 12213628026484508431410545)
                  ·
                    refine ⟨9160221019863381323557909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12213628026484508431410545 9160221019863381323557909)
                    ·
                      refine ⟨429385360306095999541777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9160221019863381323557909 429385360306095999541777)
                      ·
                        rfl

theorem cell23_836225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_836225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836225 prefixEnd_836225 := by exact prefixLift 836225
  have htrace : WordTrace (prefixWord ++ tailWord_836225) baseStart_836225 baseEnd_836225 := by
    simpa [prefixWord, tailWord_836225, baseEnd_836225] using wordTrace_append hprefix tailTrace_836225
  have hstable : (prefixWord ++ tailWord_836225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836225).length < 2 ^ (prefixWord ++ tailWord_836225).sum := by decide
  have hdescent : baseEnd_836225 < baseStart_836225 := by decide
  rcases family_descends (prefixWord ++ tailWord_836225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836252 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 3, 5]
def baseStart_836252 : Nat := 118140960795 + 836252 * 2 ^ 59
def prefixEnd_836252 : Nat := 4983230072969 + 3 ^ 40 * 836252 * 2
def baseEnd_836252 : Nat := 143133074761255797968051

theorem tailTrace_836252 : CollatzResearch.WordTrace tailWord_836252 prefixEnd_836252 143133074761255797968051 := by
  unfold tailWord_836252
  simp only [CollatzResearch.WordTrace]
  refine ⟨15250308083204649658095505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20333744110939532877460673 15250308083204649658095505)
  ·
    refine ⟨11437731062403487243571629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15250308083204649658095505 11437731062403487243571629)
    ·
      refine ⟨4289149148401307716339361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11437731062403487243571629 4289149148401307716339361)
      ·
        refine ⟨3216861861300980787254521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4289149148401307716339361 3216861861300980787254521)
        ·
          refine ⟨2412646395975735590440891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3216861861300980787254521 2412646395975735590440891)
          ·
            refine ⟨3618969593963603385661337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412646395975735590440891 3618969593963603385661337)
            ·
              refine ⟨2714227195472702539246003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3618969593963603385661337 2714227195472702539246003)
              ·
                refine ⟨4071340793209053808869005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714227195472702539246003 4071340793209053808869005)
                ·
                  refine ⟨1526752797453395178325877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4071340793209053808869005 1526752797453395178325877)
                  ·
                    refine ⟨143133074761255797968051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1526752797453395178325877 143133074761255797968051)
                    ·
                      rfl

theorem cell23_836252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_836252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836252 prefixEnd_836252 := by exact prefixLift 836252
  have htrace : WordTrace (prefixWord ++ tailWord_836252) baseStart_836252 baseEnd_836252 := by
    simpa [prefixWord, tailWord_836252, baseEnd_836252] using wordTrace_append hprefix tailTrace_836252
  have hstable : (prefixWord ++ tailWord_836252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836252).length < 2 ^ (prefixWord ++ tailWord_836252).sum := by decide
  have hdescent : baseEnd_836252 < baseStart_836252 := by decide
  rcases family_descends (prefixWord ++ tailWord_836252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836269 : List Nat := [1, 5, 2, 1, 1, 3, 1, 3, 1, 5]
def baseStart_836269 : Nat := 118140960795 + 836269 * 2 ^ 59
def prefixEnd_836269 : Nat := 4983230072969 + 3 ^ 40 * 836269 * 2
def baseEnd_836269 : Nat := 143135984484964609130525

theorem tailTrace_836269 : CollatzResearch.WordTrace tailWord_836269 prefixEnd_836269 143135984484964609130525 := by
  unfold tailWord_836269
  simp only [CollatzResearch.WordTrace]
  refine ⟨30501236207347711219559861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20334157471565140813039907 30501236207347711219559861)
  ·
    refine ⟨2859490894438847926833737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30501236207347711219559861 2859490894438847926833737)
    ·
      refine ⟨2144618170829135945125303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2859490894438847926833737 2144618170829135945125303)
      ·
        refine ⟨3216927256243703917687955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2144618170829135945125303 3216927256243703917687955)
        ·
          refine ⟨4825390884365555876531933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3216927256243703917687955 4825390884365555876531933)
          ·
            refine ⟨1809521581637083453699475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4825390884365555876531933 1809521581637083453699475)
            ·
              refine ⟨2714282372455625180549213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809521581637083453699475 2714282372455625180549213)
              ·
                refine ⟨1017855889670859442705955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2714282372455625180549213 1017855889670859442705955)
                ·
                  refine ⟨1526783834506289164058933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017855889670859442705955 1526783834506289164058933)
                  ·
                    refine ⟨143135984484964609130525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1526783834506289164058933 143135984484964609130525)
                    ·
                      rfl

theorem cell23_836269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_836269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836269 prefixEnd_836269 := by exact prefixLift 836269
  have htrace : WordTrace (prefixWord ++ tailWord_836269) baseStart_836269 baseEnd_836269 := by
    simpa [prefixWord, tailWord_836269, baseEnd_836269] using wordTrace_append hprefix tailTrace_836269
  have hstable : (prefixWord ++ tailWord_836269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836269).length < 2 ^ (prefixWord ++ tailWord_836269).sum := by decide
  have hdescent : baseEnd_836269 < baseStart_836269 := by decide
  rcases family_descends (prefixWord ++ tailWord_836269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836282 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 4, 4]
def baseStart_836282 : Nat := 118140960795 + 836282 * 2 ^ 59
def prefixEnd_836282 : Nat := 4983230072969 + 3 ^ 40 * 836282 * 2
def baseEnd_836282 : Nat := 143138209567800758843005

theorem tailTrace_836282 : CollatzResearch.WordTrace tailWord_836282 prefixEnd_836282 143138209567800758843005 := by
  unfold tailWord_836282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7625427589075153609945775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20334473570867076293188733 7625427589075153609945775)
  ·
    refine ⟨11438141383612730414918663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7625427589075153609945775 11438141383612730414918663)
    ·
      refine ⟨17157212075419095622377995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11438141383612730414918663 17157212075419095622377995)
      ·
        refine ⟨25735818113128643433566993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17157212075419095622377995 25735818113128643433566993)
        ·
          refine ⟨19301863584846482575175245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25735818113128643433566993 19301863584846482575175245)
          ·
            refine ⟨7238198844317430965690717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19301863584846482575175245 7238198844317430965690717)
            ·
              refine ⟨2714324566619036612134019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7238198844317430965690717 2714324566619036612134019)
              ·
                refine ⟨4071486849928554918201029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714324566619036612134019 4071486849928554918201029)
                ·
                  refine ⟨763403784361604047162693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4071486849928554918201029 763403784361604047162693)
                  ·
                    refine ⟨143138209567800758843005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 763403784361604047162693 143138209567800758843005)
                    ·
                      rfl

theorem cell23_836282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_836282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836282 prefixEnd_836282 := by exact prefixLift 836282
  have htrace : WordTrace (prefixWord ++ tailWord_836282) baseStart_836282 baseEnd_836282 := by
    simpa [prefixWord, tailWord_836282, baseEnd_836282] using wordTrace_append hprefix tailTrace_836282
  have hstable : (prefixWord ++ tailWord_836282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836282).length < 2 ^ (prefixWord ++ tailWord_836282).sum := by decide
  have hdescent : baseEnd_836282 < baseStart_836282 := by decide
  rcases family_descends (prefixWord ++ tailWord_836282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836292 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_836292 : Nat := 118140960795 + 836292 * 2 ^ 59
def prefixEnd_836292 : Nat := 4983230072969 + 3 ^ 40 * 836292 * 2
def baseEnd_836292 : Nat := 429419763509947237403969

theorem tailTrace_836292 : CollatzResearch.WordTrace tailWord_836292 prefixEnd_836292 429419763509947237403969 := by
  unfold tailWord_836292
  simp only [CollatzResearch.WordTrace]
  refine ⟨15251037543132193073823565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20334716724176257431764753 15251037543132193073823565)
  ·
    refine ⟨5719139078674572402683837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15251037543132193073823565 5719139078674572402683837)
    ·
      refine ⟨2144677154502964651006439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5719139078674572402683837 2144677154502964651006439)
      ·
        refine ⟨3217015731754446976509659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2144677154502964651006439 3217015731754446976509659)
        ·
          refine ⟨4825523597631670464764489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3217015731754446976509659 4825523597631670464764489)
          ·
            refine ⟨3619142698223752848573367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4825523597631670464764489 3619142698223752848573367)
            ·
              refine ⟨5428714047335629272860051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619142698223752848573367 5428714047335629272860051)
              ·
                refine ⟨8143071071003443909290077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5428714047335629272860051 8143071071003443909290077)
                ·
                  refine ⟨3053651651626291465983779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8143071071003443909290077 3053651651626291465983779)
                  ·
                    refine ⟨4580477477439437198975669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3053651651626291465983779 4580477477439437198975669)
                    ·
                      refine ⟨429419763509947237403969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4580477477439437198975669 429419763509947237403969)
                      ·
                        rfl

theorem cell23_836292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_836292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836292 prefixEnd_836292 := by exact prefixLift 836292
  have htrace : WordTrace (prefixWord ++ tailWord_836292) baseStart_836292 baseEnd_836292 := by
    simpa [prefixWord, tailWord_836292, baseEnd_836292] using wordTrace_append hprefix tailTrace_836292
  have hstable : (prefixWord ++ tailWord_836292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836292).length < 2 ^ (prefixWord ++ tailWord_836292).sum := by decide
  have hdescent : baseEnd_836292 < baseStart_836292 := by decide
  rcases family_descends (prefixWord ++ tailWord_836292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836302 : List Nat := [4, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_836302 : Nat := 118140960795 + 836302 * 2 ^ 59
def prefixEnd_836302 : Nat := 4983230072969 + 3 ^ 40 * 836302 * 2
def baseEnd_836302 : Nat := 429424898316492198278923

theorem tailTrace_836302 : CollatzResearch.WordTrace tailWord_836302 prefixEnd_836302 429424898316492198278923 := by
  unfold tailWord_836302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3812804977028519731938895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20334959877485438570340773 3812804977028519731938895)
  ·
    refine ⟨5719207465542779597908343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3812804977028519731938895 5719207465542779597908343)
    ·
      refine ⟨8578811198314169396862515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5719207465542779597908343 8578811198314169396862515)
      ·
        refine ⟨12868216797471254095293773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8578811198314169396862515 12868216797471254095293773)
        ·
          refine ⟨4825581299051720285735165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12868216797471254095293773 4825581299051720285735165)
          ·
            refine ⟨1809592987144395107150687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4825581299051720285735165 1809592987144395107150687)
            ·
              refine ⟨2714389480716592660726031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809592987144395107150687 2714389480716592660726031)
              ·
                refine ⟨4071584221074888991089047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714389480716592660726031 4071584221074888991089047)
                ·
                  refine ⟨6107376331612333486633571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4071584221074888991089047 6107376331612333486633571)
                  ·
                    refine ⟨9161064497418500229950357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6107376331612333486633571 9161064497418500229950357)
                    ·
                      refine ⟨429424898316492198278923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9161064497418500229950357 429424898316492198278923)
                      ·
                        rfl

theorem cell23_836302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_836302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836302 prefixEnd_836302 := by exact prefixLift 836302
  have htrace : WordTrace (prefixWord ++ tailWord_836302) baseStart_836302 baseEnd_836302 := by
    simpa [prefixWord, tailWord_836302, baseEnd_836302] using wordTrace_append hprefix tailTrace_836302
  have hstable : (prefixWord ++ tailWord_836302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836302).length < 2 ^ (prefixWord ++ tailWord_836302).sum := by decide
  have hdescent : baseEnd_836302 < baseStart_836302 := by decide
  rcases family_descends (prefixWord ++ tailWord_836302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836306 : List Nat := [3, 2, 2, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_836306 : Nat := 118140960795 + 836306 * 2 ^ 59
def prefixEnd_836306 : Nat := 4983230072969 + 3 ^ 40 * 836306 * 2
def baseEnd_836306 : Nat := 429426952239110182628905

theorem tailTrace_836306 : CollatzResearch.WordTrace tailWord_836306 prefixEnd_836306 429426952239110182628905 := by
  unfold tailWord_836306
  simp only [CollatzResearch.WordTrace]
  refine ⟨7625646427053416634664193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20335057138809111025771181 7625646427053416634664193)
  ·
    refine ⟨5719234820290062475998145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7625646427053416634664193 5719234820290062475998145)
    ·
      refine ⟨4289426115217546856998609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5719234820290062475998145 4289426115217546856998609)
      ·
        refine ⟨3217069586413160142748957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4289426115217546856998609 3217069586413160142748957)
        ·
          refine ⟨1206401094904935053530859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3217069586413160142748957 1206401094904935053530859)
          ·
            refine ⟨1809601642357402580296289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206401094904935053530859 1809601642357402580296289)
            ·
              refine ⟨1357201231768051935222217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1809601642357402580296289 1357201231768051935222217)
              ·
                refine ⟨1017900923826038951416663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1357201231768051935222217 1017900923826038951416663)
                ·
                  refine ⟨1526851385739058427124995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017900923826038951416663 1526851385739058427124995)
                  ·
                    refine ⟨2290277078608587640687493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1526851385739058427124995 2290277078608587640687493)
                    ·
                      refine ⟨429426952239110182628905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2290277078608587640687493 429426952239110182628905)
                      ·
                        rfl

theorem cell23_836306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_836306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836306 prefixEnd_836306 := by exact prefixLift 836306
  have htrace : WordTrace (prefixWord ++ tailWord_836306) baseStart_836306 baseEnd_836306 := by
    simpa [prefixWord, tailWord_836306, baseEnd_836306] using wordTrace_append hprefix tailTrace_836306
  have hstable : (prefixWord ++ tailWord_836306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836306).length < 2 ^ (prefixWord ++ tailWord_836306).sum := by decide
  have hdescent : baseEnd_836306 < baseStart_836306 := by decide
  rcases family_descends (prefixWord ++ tailWord_836306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836312 : List Nat := [2, 1, 2, 2, 3, 2, 4, 7]
def baseStart_836312 : Nat := 118140960795 + 836312 * 2 ^ 59
def prefixEnd_836312 : Nat := 4983230072969 + 3 ^ 40 * 836312 * 2
def baseEnd_836312 : Nat := 15904816041593968857551

theorem tailTrace_836312 : CollatzResearch.WordTrace tailWord_836312 prefixEnd_836312 15904816041593968857551 := by
  unfold tailWord_836312
  simp only [CollatzResearch.WordTrace]
  refine ⟨15251402273095964781687595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20335203030794619708916793 15251402273095964781687595)
  ·
    refine ⟨22877103409643947172531393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15251402273095964781687595 22877103409643947172531393)
    ·
      refine ⟨17157827557232960379398545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22877103409643947172531393 17157827557232960379398545)
      ·
        refine ⟨12868370667924720284548909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17157827557232960379398545 12868370667924720284548909)
        ·
          refine ⟨4825639000471770106705841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12868370667924720284548909 4825639000471770106705841)
          ·
            refine ⟨3619229250353827580029381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4825639000471770106705841 3619229250353827580029381)
            ·
              refine ⟨678605484441342671255509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3619229250353827580029381 678605484441342671255509)
              ·
                refine ⟨15904816041593968857551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 678605484441342671255509 15904816041593968857551)
                ·
                  rfl

theorem cell23_836312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 4, 7].length) (baseStart_836312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836312 prefixEnd_836312 := by exact prefixLift 836312
  have htrace : WordTrace (prefixWord ++ tailWord_836312) baseStart_836312 baseEnd_836312 := by
    simpa [prefixWord, tailWord_836312, baseEnd_836312] using wordTrace_append hprefix tailTrace_836312
  have hstable : (prefixWord ++ tailWord_836312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836312).length < 2 ^ (prefixWord ++ tailWord_836312).sum := by decide
  have hdescent : baseEnd_836312 < baseStart_836312 := by decide
  rcases family_descends (prefixWord ++ tailWord_836312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836339 : List Nat := [1, 1, 1, 2, 2, 3, 1, 6, 2, 1, 3]
def baseStart_836339 : Nat := 118140960795 + 836339 * 2 ^ 59
def prefixEnd_836339 : Nat := 4983230072969 + 3 ^ 40 * 836339 * 2
def baseEnd_836339 : Nat := 429443897100708553516253

theorem tailTrace_836339 : CollatzResearch.WordTrace tailWord_836339 prefixEnd_836339 429443897100708553516253 := by
  unfold tailWord_836339
  simp only [CollatzResearch.WordTrace]
  refine ⟨30503789317094113174608071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20335859544729408783072047 30503789317094113174608071)
  ·
    refine ⟨45755683975641169761912107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30503789317094113174608071 45755683975641169761912107)
    ·
      refine ⟨68633525963461754642868161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45755683975641169761912107 68633525963461754642868161)
      ·
        refine ⟨51475144472596315982151121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68633525963461754642868161 51475144472596315982151121)
        ·
          refine ⟨38606358354447236986613341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51475144472596315982151121 38606358354447236986613341)
          ·
            refine ⟨14477384382917713869980003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38606358354447236986613341 14477384382917713869980003)
            ·
              refine ⟨21716076574376570804970005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14477384382917713869980003 21716076574376570804970005)
              ·
                refine ⟨1017941089423901756482969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21716076574376570804970005 1017941089423901756482969)
                ·
                  refine ⟨763455817067926317362227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1017941089423901756482969 763455817067926317362227)
                  ·
                    refine ⟨1145183725601889476043341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 763455817067926317362227 1145183725601889476043341)
                    ·
                      refine ⟨429443897100708553516253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1145183725601889476043341 429443897100708553516253)
                      ·
                        rfl

theorem cell23_836339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2, 1, 3].length) (baseStart_836339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836339 prefixEnd_836339 := by exact prefixLift 836339
  have htrace : WordTrace (prefixWord ++ tailWord_836339) baseStart_836339 baseEnd_836339 := by
    simpa [prefixWord, tailWord_836339, baseEnd_836339] using wordTrace_append hprefix tailTrace_836339
  have hstable : (prefixWord ++ tailWord_836339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836339).length < 2 ^ (prefixWord ++ tailWord_836339).sum := by decide
  have hdescent : baseEnd_836339 < baseStart_836339 := by decide
  rcases family_descends (prefixWord ++ tailWord_836339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836342 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_836342 : Nat := 118140960795 + 836342 * 2 ^ 59
def prefixEnd_836342 : Nat := 4983230072969 + 3 ^ 40 * 836342 * 2
def baseEnd_836342 : Nat := 143148479180890680592913

theorem tailTrace_836342 : CollatzResearch.WordTrace tailWord_836342 prefixEnd_836342 143148479180890680592913 := by
  unfold tailWord_836342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906493671005202792935455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20335932490722163124644853 1906493671005202792935455)
  ·
    refine ⟨2859740506507804189403183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1906493671005202792935455 2859740506507804189403183)
    ·
      refine ⟨4289610759761706284104775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2859740506507804189403183 4289610759761706284104775)
      ·
        refine ⟨6434416139642559426157163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4289610759761706284104775 6434416139642559426157163)
        ·
          refine ⟨9651624209463839139235745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6434416139642559426157163 9651624209463839139235745)
          ·
            refine ⟨7238718157097879354426809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9651624209463839139235745 7238718157097879354426809)
            ·
              refine ⟨5429038617823409515820107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7238718157097879354426809 5429038617823409515820107)
              ·
                refine ⟨8143557926735114273730161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5429038617823409515820107 8143557926735114273730161)
                ·
                  refine ⟨6107668445051335705297621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8143557926735114273730161 6107668445051335705297621)
                  ·
                    refine ⟨143148479180890680592913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6107668445051335705297621 143148479180890680592913)
                    ·
                      rfl

theorem cell23_836342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_836342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836342 prefixEnd_836342 := by exact prefixLift 836342
  have htrace : WordTrace (prefixWord ++ tailWord_836342) baseStart_836342 baseEnd_836342 := by
    simpa [prefixWord, tailWord_836342, baseEnd_836342] using wordTrace_append hprefix tailTrace_836342
  have hstable : (prefixWord ++ tailWord_836342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836342).length < 2 ^ (prefixWord ++ tailWord_836342).sum := by decide
  have hdescent : baseEnd_836342 < baseStart_836342 := by decide
  rcases family_descends (prefixWord ++ tailWord_836342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836349 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 3, 3, 2]
def baseStart_836349 : Nat := 118140960795 + 836349 * 2 ^ 59
def prefixEnd_836349 : Nat := 4983230072969 + 3 ^ 40 * 836349 * 2
def baseEnd_836349 : Nat := 429449031907253514391207

theorem tailTrace_836349 : CollatzResearch.WordTrace tailWord_836349 prefixEnd_836349 429449031907253514391207 := by
  unfold tailWord_836349
  simp only [CollatzResearch.WordTrace]
  refine ⟨30504154047057884882472101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20336102698038589921648067 30504154047057884882472101)
  ·
    refine ⟨5719528883823353415463519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30504154047057884882472101 5719528883823353415463519)
    ·
      refine ⟨8579293325735030123195279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5719528883823353415463519 8579293325735030123195279)
      ·
        refine ⟨12868939988602545184792919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8579293325735030123195279 12868939988602545184792919)
        ·
          refine ⟨19303409982903817777189379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12868939988602545184792919 19303409982903817777189379)
          ·
            refine ⟨28955114974355726665784069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19303409982903817777189379 28955114974355726665784069)
            ·
              refine ⟨5429084057691698749834513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28955114974355726665784069 5429084057691698749834513)
              ·
                refine ⟨4071813043268774062375885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5429084057691698749834513 4071813043268774062375885)
                ·
                  refine ⟨1526929891225790273390957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4071813043268774062375885 1526929891225790273390957)
                  ·
                    refine ⟨572598709209671352521609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1526929891225790273390957 572598709209671352521609)
                    ·
                      refine ⟨429449031907253514391207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 572598709209671352521609 429449031907253514391207)
                      ·
                        rfl

theorem cell23_836349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_836349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836349 prefixEnd_836349 := by exact prefixLift 836349
  have htrace : WordTrace (prefixWord ++ tailWord_836349) baseStart_836349 baseEnd_836349 := by
    simpa [prefixWord, tailWord_836349, baseEnd_836349] using wordTrace_append hprefix tailTrace_836349
  have hstable : (prefixWord ++ tailWord_836349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836349).length < 2 ^ (prefixWord ++ tailWord_836349).sum := by decide
  have hdescent : baseEnd_836349 < baseStart_836349 := by decide
  rcases family_descends (prefixWord ++ tailWord_836349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836355 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 1, 8]
def baseStart_836355 : Nat := 118140960795 + 836355 * 2 ^ 59
def prefixEnd_836355 : Nat := 4983230072969 + 3 ^ 40 * 836355 * 2
def baseEnd_836355 : Nat := 143150704263726830305393

theorem tailTrace_836355 : CollatzResearch.WordTrace tailWord_836355 prefixEnd_836355 143150704263726830305393 := by
  unfold tailWord_836355
  simp only [CollatzResearch.WordTrace]
  refine ⟨30504372885036147907190519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20336248590024098604793679 30504372885036147907190519)
  ·
    refine ⟨45756559327554221860785779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30504372885036147907190519 45756559327554221860785779)
    ·
      refine ⟨68634838991331332791178669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45756559327554221860785779 68634838991331332791178669)
      ·
        refine ⟨25738064621749249796692001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68634838991331332791178669 25738064621749249796692001)
        ·
          refine ⟨19303548466311937347519001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25738064621749249796692001 19303548466311937347519001)
          ·
            refine ⟨14477661349733953010639251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19303548466311937347519001 14477661349733953010639251)
            ·
              refine ⟨21716492024600929515958877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14477661349733953010639251 21716492024600929515958877)
              ·
                refine ⟨8143684509225348568484579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21716492024600929515958877 8143684509225348568484579)
                ·
                  refine ⟨12215526763838022852726869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8143684509225348568484579 12215526763838022852726869)
                  ·
                    refine ⟨143150704263726830305393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12215526763838022852726869 143150704263726830305393)
                    ·
                      rfl

theorem cell23_836355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 8].length) (baseStart_836355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836355 prefixEnd_836355 := by exact prefixLift 836355
  have htrace : WordTrace (prefixWord ++ tailWord_836355) baseStart_836355 baseEnd_836355 := by
    simpa [prefixWord, tailWord_836355, baseEnd_836355] using wordTrace_append hprefix tailTrace_836355
  have hstable : (prefixWord ++ tailWord_836355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836355).length < 2 ^ (prefixWord ++ tailWord_836355).sum := by decide
  have hdescent : baseEnd_836355 < baseStart_836355 := by decide
  rcases family_descends (prefixWord ++ tailWord_836355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836356 : List Nat := [2, 3, 2, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_836356 : Nat := 118140960795 + 836356 * 2 ^ 59
def prefixEnd_836356 : Nat := 4983230072969 + 3 ^ 40 * 836356 * 2
def baseEnd_836356 : Nat := 429452626271834987003675

theorem tailTrace_836356 : CollatzResearch.WordTrace tailWord_836356 prefixEnd_836356 429452626271834987003675 := by
  unfold tailWord_836356
  simp only [CollatzResearch.WordTrace]
  refine ⟨15252204679016262538988461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20336272905355016718651281 15252204679016262538988461)
  ·
    refine ⟨5719576754631098452120673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15252204679016262538988461 5719576754631098452120673)
    ·
      refine ⟨4289682565973323839090505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5719576754631098452120673 4289682565973323839090505)
      ·
        refine ⟨3217261924479992879317879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4289682565973323839090505 3217261924479992879317879)
        ·
          refine ⟨4825892886719989318976819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3217261924479992879317879 4825892886719989318976819)
          ·
            refine ⟨7238839330079983978465229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4825892886719989318976819 7238839330079983978465229)
            ·
              refine ⟨2714564748779993991924461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7238839330079983978465229 2714564748779993991924461)
              ·
                refine ⟨1017961780792497746971673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2714564748779993991924461 1017961780792497746971673)
                ·
                  refine ⟨763471335594373310228755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1017961780792497746971673 763471335594373310228755)
                  ·
                    refine ⟨1145207003391559965343133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 763471335594373310228755 1145207003391559965343133)
                    ·
                      refine ⟨429452626271834987003675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1145207003391559965343133 429452626271834987003675)
                      ·
                        rfl

theorem cell23_836356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_836356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836356 prefixEnd_836356 := by exact prefixLift 836356
  have htrace : WordTrace (prefixWord ++ tailWord_836356) baseStart_836356 baseEnd_836356 := by
    simpa [prefixWord, tailWord_836356, baseEnd_836356] using wordTrace_append hprefix tailTrace_836356
  have hstable : (prefixWord ++ tailWord_836356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836356).length < 2 ^ (prefixWord ++ tailWord_836356).sum := by decide
  have hdescent : baseEnd_836356 < baseStart_836356 := by decide
  rcases family_descends (prefixWord ++ tailWord_836356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836383 : List Nat := [1, 1, 2, 4, 2, 3, 3, 1, 1, 3, 2]
def baseStart_836383 : Nat := 118140960795 + 836383 * 2 ^ 59
def prefixEnd_836383 : Nat := 4983230072969 + 3 ^ 40 * 836383 * 2
def baseEnd_836383 : Nat := 429466490249506381366051

theorem tailTrace_836383 : CollatzResearch.WordTrace tailWord_836383 prefixEnd_836383 429466490249506381366051 := by
  unfold tailWord_836383
  simp only [CollatzResearch.WordTrace]
  refine ⟨30505394128934708689209803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20336929419289805792806535 30505394128934708689209803)
  ·
    refine ⟨45758091193402063033814705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30505394128934708689209803 45758091193402063033814705)
    ·
      refine ⟨34318568395051547275361029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45758091193402063033814705 34318568395051547275361029)
      ·
        refine ⟨6434731574072165114130193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34318568395051547275361029 6434731574072165114130193)
        ·
          refine ⟨4826048680554123835597645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6434731574072165114130193 4826048680554123835597645)
          ·
            refine ⟨1809768255207796438349117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4826048680554123835597645 1809768255207796438349117)
            ·
              refine ⟨678663095702923664380919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1809768255207796438349117 678663095702923664380919)
              ·
                refine ⟨1017994643554385496571379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678663095702923664380919 1017994643554385496571379)
                ·
                  refine ⟨1526991965331578244857069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017994643554385496571379 1526991965331578244857069)
                  ·
                    refine ⟨572621986999341841821401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1526991965331578244857069 572621986999341841821401)
                    ·
                      refine ⟨429466490249506381366051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 572621986999341841821401 429466490249506381366051)
                      ·
                        rfl

theorem cell23_836383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_836383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836383 prefixEnd_836383 := by exact prefixLift 836383
  have htrace : WordTrace (prefixWord ++ tailWord_836383) baseStart_836383 baseEnd_836383 := by
    simpa [prefixWord, tailWord_836383, baseEnd_836383] using wordTrace_append hprefix tailTrace_836383
  have hstable : (prefixWord ++ tailWord_836383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836383).length < 2 ^ (prefixWord ++ tailWord_836383).sum := by decide
  have hdescent : baseEnd_836383 < baseStart_836383 := by decide
  rcases family_descends (prefixWord ++ tailWord_836383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836395 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 9]
def baseStart_836395 : Nat := 118140960795 + 836395 * 2 ^ 59
def prefixEnd_836395 : Nat := 4983230072969 + 3 ^ 40 * 836395 * 2
def baseEnd_836395 : Nat := 429472652017360334415995

theorem tailTrace_836395 : CollatzResearch.WordTrace tailWord_836395 prefixEnd_836395 429472652017360334415995 := by
  unfold tailWord_836395
  simp only [CollatzResearch.WordTrace]
  refine ⟨30505831804891234738646639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20337221203260823159097759 30505831804891234738646639)
  ·
    refine ⟨45758747707336852107969959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30505831804891234738646639 45758747707336852107969959)
    ·
      refine ⟨68638121561005278161954939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45758747707336852107969959 68638121561005278161954939)
      ·
        refine ⟨102957182341507917242932409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68638121561005278161954939 102957182341507917242932409)
        ·
          refine ⟨77217886756130937932199307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102957182341507917242932409 77217886756130937932199307)
          ·
            refine ⟨115826830134196406898298961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77217886756130937932199307 115826830134196406898298961)
            ·
              refine ⟨86870122600647305173724221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115826830134196406898298961 86870122600647305173724221)
              ·
                refine ⟨32576295975242739440146583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86870122600647305173724221 32576295975242739440146583)
                ·
                  refine ⟨48864443962864109160219875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32576295975242739440146583 48864443962864109160219875)
                  ·
                    refine ⟨73296665944296163740329813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48864443962864109160219875 73296665944296163740329813)
                    ·
                      refine ⟨429472652017360334415995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 73296665944296163740329813 429472652017360334415995)
                      ·
                        rfl

theorem cell23_836395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_836395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836395 prefixEnd_836395 := by exact prefixLift 836395
  have htrace : WordTrace (prefixWord ++ tailWord_836395) baseStart_836395 baseEnd_836395 := by
    simpa [prefixWord, tailWord_836395, baseEnd_836395] using wordTrace_append hprefix tailTrace_836395
  have hstable : (prefixWord ++ tailWord_836395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836395).length < 2 ^ (prefixWord ++ tailWord_836395).sum := by decide
  have hdescent : baseEnd_836395 < baseStart_836395 := by decide
  rcases family_descends (prefixWord ++ tailWord_836395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836402 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 7]
def baseStart_836402 : Nat := 118140960795 + 836402 * 2 ^ 59
def prefixEnd_836402 : Nat := 4983230072969 + 3 ^ 40 * 836402 * 2
def baseEnd_836402 : Nat := 47719582931326867447607

theorem tailTrace_836402 : CollatzResearch.WordTrace tailWord_836402 prefixEnd_836402 47719582931326867447607 := by
  unfold tailWord_836402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7626521778966468733537865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20337391410577249956100973 7626521778966468733537865)
  ·
    refine ⟨5719891334224851550153399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7626521778966468733537865 5719891334224851550153399)
    ·
      refine ⟨8579837001337277325230099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5719891334224851550153399 8579837001337277325230099)
      ·
        refine ⟨12869755502005915987845149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8579837001337277325230099 12869755502005915987845149)
        ·
          refine ⟨4826158313252218495441931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12869755502005915987845149 4826158313252218495441931)
          ·
            refine ⟨7239237469878327743162897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826158313252218495441931 7239237469878327743162897)
            ·
              refine ⟨5429428102408745807372173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7239237469878327743162897 5429428102408745807372173)
              ·
                refine ⟨2036035538403279677764565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5429428102408745807372173 2036035538403279677764565)
                ·
                  refine ⟨47719582931326867447607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2036035538403279677764565 47719582931326867447607)
                  ·
                    rfl

theorem cell23_836402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_836402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836402 prefixEnd_836402 := by exact prefixLift 836402
  have htrace : WordTrace (prefixWord ++ tailWord_836402) baseStart_836402 baseEnd_836402 := by
    simpa [prefixWord, tailWord_836402, baseEnd_836402] using wordTrace_append hprefix tailTrace_836402
  have hstable : (prefixWord ++ tailWord_836402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836402).length < 2 ^ (prefixWord ++ tailWord_836402).sum := by decide
  have hdescent : baseEnd_836402 < baseStart_836402 := by decide
  rcases family_descends (prefixWord ++ tailWord_836402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836406 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_836406 : Nat := 118140960795 + 836406 * 2 ^ 59
def prefixEnd_836406 : Nat := 4983230072969 + 3 ^ 40 * 836406 * 2
def baseEnd_836406 : Nat := 143159433434853263792815

theorem tailTrace_836406 : CollatzResearch.WordTrace tailWord_836406 prefixEnd_836406 143159433434853263792815 := by
  unfold tailWord_836406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906639562990711476081067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20337488671900922411531381 1906639562990711476081067)
  ·
    refine ⟨2859959344486067214121601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1906639562990711476081067 2859959344486067214121601)
    ·
      refine ⟨2144969508364550410591201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2859959344486067214121601 2144969508364550410591201)
      ·
        refine ⟨1608727131273412807943401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2144969508364550410591201 1608727131273412807943401)
        ·
          refine ⟨1206545348455059605957551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1608727131273412807943401 1206545348455059605957551)
          ·
            refine ⟨1809818022682589408936327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206545348455059605957551 1809818022682589408936327)
            ·
              refine ⟨2714727034023884113404491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809818022682589408936327 2714727034023884113404491)
              ·
                refine ⟨4072090551035826170106737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714727034023884113404491 4072090551035826170106737)
                ·
                  refine ⟨3054067913276869627580053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4072090551035826170106737 3054067913276869627580053)
                  ·
                    refine ⟨143159433434853263792815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3054067913276869627580053 143159433434853263792815)
                    ·
                      rfl

theorem cell23_836406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_836406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836406 prefixEnd_836406 := by exact prefixLift 836406
  have htrace : WordTrace (prefixWord ++ tailWord_836406) baseStart_836406 baseEnd_836406 := by
    simpa [prefixWord, tailWord_836406, baseEnd_836406] using wordTrace_append hprefix tailTrace_836406
  have hstable : (prefixWord ++ tailWord_836406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836406).length < 2 ^ (prefixWord ++ tailWord_836406).sum := by decide
  have hdescent : baseEnd_836406 < baseStart_836406 := by decide
  rcases family_descends (prefixWord ++ tailWord_836406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836413 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 1, 4, 2]
def baseStart_836413 : Nat := 118140960795 + 836413 * 2 ^ 59
def prefixEnd_836413 : Nat := 4983230072969 + 3 ^ 40 * 836413 * 2
def baseEnd_836413 : Nat := 429481894669141263990913

theorem tailTrace_836413 : CollatzResearch.WordTrace tailWord_836413 prefixEnd_836413 429481894669141263990913 := by
  unfold tailWord_836413
  simp only [CollatzResearch.WordTrace]
  refine ⟨30506488318826023812801893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20337658879217349208534595 30506488318826023812801893)
  ·
    refine ⟨5719966559779879464900355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30506488318826023812801893 5719966559779879464900355)
    ·
      refine ⟨8579949839669819197350533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5719966559779879464900355 8579949839669819197350533)
      ·
        refine ⟨1608740594938091099503225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8579949839669819197350533 1608740594938091099503225)
        ·
          refine ⟨1206555446203568324627419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1608740594938091099503225 1206555446203568324627419)
          ·
            refine ⟨1809833169305352486941129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206555446203568324627419 1809833169305352486941129)
            ·
              refine ⟨1357374876979014365205847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1809833169305352486941129 1357374876979014365205847)
              ·
                refine ⟨2036062315468521547808771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357374876979014365205847 2036062315468521547808771)
                ·
                  refine ⟨3054093473202782321713157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036062315468521547808771 3054093473202782321713157)
                  ·
                    refine ⟨572642526225521685321217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3054093473202782321713157 572642526225521685321217)
                    ·
                      refine ⟨429481894669141263990913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 572642526225521685321217 429481894669141263990913)
                      ·
                        rfl

theorem cell23_836413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_836413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836413 prefixEnd_836413 := by exact prefixLift 836413
  have htrace : WordTrace (prefixWord ++ tailWord_836413) baseStart_836413 baseEnd_836413 := by
    simpa [prefixWord, tailWord_836413, baseEnd_836413] using wordTrace_append hprefix tailTrace_836413
  have hstable : (prefixWord ++ tailWord_836413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836413).length < 2 ^ (prefixWord ++ tailWord_836413).sum := by decide
  have hdescent : baseEnd_836413 < baseStart_836413 := by decide
  rcases family_descends (prefixWord ++ tailWord_836413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836469 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_836469 : Nat := 118140960795 + 836469 * 2 ^ 59
def prefixEnd_836469 : Nat := 4983230072969 + 3 ^ 40 * 836469 * 2
def baseEnd_836469 : Nat := 429510649585793044890655

theorem tailTrace_836469 : CollatzResearch.WordTrace tailWord_836469 prefixEnd_836469 429510649585793044890655 := by
  unfold tailWord_836469
  simp only [CollatzResearch.WordTrace]
  refine ⟨30508530806623145376840461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20339020537748763584560307 30508530806623145376840461)
  ·
    refine ⟨11440699052483679516315173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30508530806623145376840461 11440699052483679516315173)
    ·
      refine ⟨2145131072340689909309095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11440699052483679516315173 2145131072340689909309095)
      ·
        refine ⟨3217696608511034863963643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145131072340689909309095 3217696608511034863963643)
        ·
          refine ⟨4826544912766552295945465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3217696608511034863963643 4826544912766552295945465)
          ·
            refine ⟨3619908684574914221959099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4826544912766552295945465 3619908684574914221959099)
            ·
              refine ⟨5429863026862371332938649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619908684574914221959099 5429863026862371332938649)
              ·
                refine ⟨4072397270146778499703987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5429863026862371332938649 4072397270146778499703987)
                ·
                  refine ⟨6108595905220167749555981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4072397270146778499703987 6108595905220167749555981)
                  ·
                    refine ⟨2290723464457562906083493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6108595905220167749555981 2290723464457562906083493)
                    ·
                      refine ⟨429510649585793044890655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2290723464457562906083493 429510649585793044890655)
                      ·
                        rfl

theorem cell23_836469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_836469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836469 prefixEnd_836469 := by exact prefixLift 836469
  have htrace : WordTrace (prefixWord ++ tailWord_836469) baseStart_836469 baseEnd_836469 := by
    simpa [prefixWord, tailWord_836469, baseEnd_836469] using wordTrace_append hprefix tailTrace_836469
  have hstable : (prefixWord ++ tailWord_836469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836469).length < 2 ^ (prefixWord ++ tailWord_836469).sum := by decide
  have hdescent : baseEnd_836469 < baseStart_836469 := by decide
  rcases family_descends (prefixWord ++ tailWord_836469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836479 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 3, 4]
def baseStart_836479 : Nat := 118140960795 + 836479 * 2 ^ 59
def prefixEnd_836479 : Nat := 4983230072969 + 3 ^ 40 * 836479 * 2
def baseEnd_836479 : Nat := 143171928130779335255203

theorem tailTrace_836479 : CollatzResearch.WordTrace tailWord_836479 prefixEnd_836479 143171928130779335255203 := by
  unfold tailWord_836479
  simp only [CollatzResearch.WordTrace]
  refine ⟨30508895536586917084704491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20339263691057944723136327 30508895536586917084704491)
  ·
    refine ⟨45763343304880375627056737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30508895536586917084704491 45763343304880375627056737)
    ·
      refine ⟨34322507478660281720292553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45763343304880375627056737 34322507478660281720292553)
      ·
        refine ⟨25741880608995211290219415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34322507478660281720292553 25741880608995211290219415)
        ·
          refine ⟨38612820913492816935329123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25741880608995211290219415 38612820913492816935329123)
          ·
            refine ⟨57919231370239225402993685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38612820913492816935329123 57919231370239225402993685)
            ·
              refine ⟨2714963970479963690765329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57919231370239225402993685 2714963970479963690765329)
              ·
                refine ⟨2036222977859972768073997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2714963970479963690765329 2036222977859972768073997)
                ·
                  refine ⟨763583616697489788027749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2036222977859972768073997 763583616697489788027749)
                  ·
                    refine ⟨143171928130779335255203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 763583616697489788027749 143171928130779335255203)
                    ·
                      rfl

theorem cell23_836479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 4].length) (baseStart_836479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836479 prefixEnd_836479 := by exact prefixLift 836479
  have htrace : WordTrace (prefixWord ++ tailWord_836479) baseStart_836479 baseEnd_836479 := by
    simpa [prefixWord, tailWord_836479, baseEnd_836479] using wordTrace_append hprefix tailTrace_836479
  have hstable : (prefixWord ++ tailWord_836479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836479).length < 2 ^ (prefixWord ++ tailWord_836479).sum := by decide
  have hdescent : baseEnd_836479 < baseStart_836479 := by decide
  rcases family_descends (prefixWord ++ tailWord_836479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836489 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 1, 4, 3]
def baseStart_836489 : Nat := 118140960795 + 836489 * 2 ^ 59
def prefixEnd_836489 : Nat := 4983230072969 + 3 ^ 40 * 836489 * 2
def baseEnd_836489 : Nat := 429520919198882966640563

theorem tailTrace_836489 : CollatzResearch.WordTrace tailWord_836489 prefixEnd_836489 429520919198882966640563 := by
  unfold tailWord_836489
  simp only [CollatzResearch.WordTrace]
  refine ⟨30509260266550688792568521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20339506844367125861712347 30509260266550688792568521)
  ·
    refine ⟨22881945199913016594426391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30509260266550688792568521 22881945199913016594426391)
    ·
      refine ⟨34322917799869524891639587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22881945199913016594426391 34322917799869524891639587)
      ·
        refine ⟨51484376699804287337459381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34322917799869524891639587 51484376699804287337459381)
        ·
          refine ⟨4826660315606651937886817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51484376699804287337459381 4826660315606651937886817)
          ·
            refine ⟨3619995236704988953415113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4826660315606651937886817 3619995236704988953415113)
            ·
              refine ⟨2714996427528741715061335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3619995236704988953415113 2714996427528741715061335)
              ·
                refine ⟨4072494641293112572592003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714996427528741715061335 4072494641293112572592003)
                ·
                  refine ⟨6108741961939668858888005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4072494641293112572592003 6108741961939668858888005)
                  ·
                    refine ⟨1145389117863687911041501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6108741961939668858888005 1145389117863687911041501)
                    ·
                      refine ⟨429520919198882966640563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1145389117863687911041501 429520919198882966640563)
                      ·
                        rfl

theorem cell23_836489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 4, 3].length) (baseStart_836489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836489 prefixEnd_836489 := by exact prefixLift 836489
  have htrace : WordTrace (prefixWord ++ tailWord_836489) baseStart_836489 baseEnd_836489 := by
    simpa [prefixWord, tailWord_836489, baseEnd_836489] using wordTrace_append hprefix tailTrace_836489
  have hstable : (prefixWord ++ tailWord_836489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836489).length < 2 ^ (prefixWord ++ tailWord_836489).sum := by decide
  have hdescent : baseEnd_836489 < baseStart_836489 := by decide
  rcases family_descends (prefixWord ++ tailWord_836489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836492 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 8]
def baseStart_836492 : Nat := 118140960795 + 836492 * 2 ^ 59
def prefixEnd_836492 : Nat := 4983230072969 + 3 ^ 40 * 836492 * 2
def baseEnd_836492 : Nat := 47724717737871828322561

theorem tailTrace_836492 : CollatzResearch.WordTrace tailWord_836492 prefixEnd_836492 47724717737871828322561 := by
  unfold tailWord_836492
  simp only [CollatzResearch.WordTrace]
  refine ⟨15254684842769910152463865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20339579790359880203285153 15254684842769910152463865)
  ·
    refine ⟨11441013632077432614347899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15254684842769910152463865 11441013632077432614347899)
    ·
      refine ⟨17161520448116148921521849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11441013632077432614347899 17161520448116148921521849)
      ·
        refine ⟨12871140336087111691141387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17161520448116148921521849 12871140336087111691141387)
        ·
          refine ⟨19306710504130667536712081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12871140336087111691141387 19306710504130667536712081)
          ·
            refine ⟨14480032878098000652534061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19306710504130667536712081 14480032878098000652534061)
            ·
              refine ⟨5430012329286750244700273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14480032878098000652534061 5430012329286750244700273)
              ·
                refine ⟨4072509246965062683525205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5430012329286750244700273 4072509246965062683525205)
                ·
                  refine ⟨47724717737871828322561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4072509246965062683525205 47724717737871828322561)
                  ·
                    rfl

theorem cell23_836492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_836492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836492 prefixEnd_836492 := by exact prefixLift 836492
  have htrace : WordTrace (prefixWord ++ tailWord_836492) baseStart_836492 baseEnd_836492 := by
    simpa [prefixWord, tailWord_836492, baseEnd_836492] using wordTrace_append hprefix tailTrace_836492
  have hstable : (prefixWord ++ tailWord_836492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836492).length < 2 ^ (prefixWord ++ tailWord_836492).sum := by decide
  have hdescent : baseEnd_836492 < baseStart_836492 := by decide
  rcases family_descends (prefixWord ++ tailWord_836492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836509 : List Nat := [1, 4, 2, 1, 2, 1, 2, 4, 6]
def baseStart_836509 : Nat := 118140960795 + 836509 * 2 ^ 59
def prefixEnd_836509 : Nat := 4983230072969 + 3 ^ 40 * 836509 * 2
def baseEnd_836509 : Nat := 47725687645774765376719

theorem tailTrace_836509 : CollatzResearch.WordTrace tailWord_836509 prefixEnd_836509 47725687645774765376719 := by
  unfold tailWord_836509
  simp only [CollatzResearch.WordTrace]
  refine ⟨30509989726478232208296581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20339993150985488138864387 30509989726478232208296581)
  ·
    refine ⟨5720623073714668539055609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30509989726478232208296581 5720623073714668539055609)
    ·
      refine ⟨4290467305286001404291707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5720623073714668539055609 4290467305286001404291707)
      ·
        refine ⟨6435700957929002106437561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4290467305286001404291707 6435700957929002106437561)
        ·
          refine ⟨4826775718446751579828171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6435700957929002106437561 4826775718446751579828171)
          ·
            refine ⟨7240163577670127369742257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826775718446751579828171 7240163577670127369742257)
            ·
              refine ⟨5430122683252595527306693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7240163577670127369742257 5430122683252595527306693)
              ·
                refine ⟨1018148003109861661370005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5430122683252595527306693 1018148003109861661370005)
                ·
                  refine ⟨47725687645774765376719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1018148003109861661370005 47725687645774765376719)
                  ·
                    rfl

theorem cell23_836509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_836509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836509 prefixEnd_836509 := by exact prefixLift 836509
  have htrace : WordTrace (prefixWord ++ tailWord_836509) baseStart_836509 baseEnd_836509 := by
    simpa [prefixWord, tailWord_836509, baseEnd_836509] using wordTrace_append hprefix tailTrace_836509
  have hstable : (prefixWord ++ tailWord_836509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836509).length < 2 ^ (prefixWord ++ tailWord_836509).sum := by decide
  have hdescent : baseEnd_836509 < baseStart_836509 := by decide
  rcases family_descends (prefixWord ++ tailWord_836509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836512 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 8]
def baseStart_836512 : Nat := 118140960795 + 836512 * 2 ^ 59
def prefixEnd_836512 : Nat := 4983230072969 + 3 ^ 40 * 836512 * 2
def baseEnd_836512 : Nat := 429532729253936376652957

theorem tailTrace_836512 : CollatzResearch.WordTrace tailWord_836512 prefixEnd_836512 429532729253936376652957 := by
  unfold tailWord_836512
  simp only [CollatzResearch.WordTrace]
  refine ⟨15255049572733681860327895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20340066096978242480437193 15255049572733681860327895)
  ·
    refine ⟨22882574359100522790491843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15255049572733681860327895 22882574359100522790491843)
    ·
      refine ⟨34323861538650784185737765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22882574359100522790491843 34323861538650784185737765)
      ·
        refine ⟨6435724038497022034825831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34323861538650784185737765 6435724038497022034825831)
        ·
          refine ⟨9653586057745533052238747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6435724038497022034825831 9653586057745533052238747)
          ·
            refine ⟨14480379086618299578358121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9653586057745533052238747 14480379086618299578358121)
            ·
              refine ⟨10860284314963724683768591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14480379086618299578358121 10860284314963724683768591)
              ·
                refine ⟨16290426472445587025652887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10860284314963724683768591 16290426472445587025652887)
                ·
                  refine ⟨24435639708668380538479331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16290426472445587025652887 24435639708668380538479331)
                  ·
                    refine ⟨36653459563002570807718997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24435639708668380538479331 36653459563002570807718997)
                    ·
                      refine ⟨429532729253936376652957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 36653459563002570807718997 429532729253936376652957)
                      ·
                        rfl

theorem cell23_836512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_836512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836512 prefixEnd_836512 := by exact prefixLift 836512
  have htrace : WordTrace (prefixWord ++ tailWord_836512) baseStart_836512 baseEnd_836512 := by
    simpa [prefixWord, tailWord_836512, baseEnd_836512] using wordTrace_append hprefix tailTrace_836512
  have hstable : (prefixWord ++ tailWord_836512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836512).length < 2 ^ (prefixWord ++ tailWord_836512).sum := by decide
  have hdescent : baseEnd_836512 < baseStart_836512 := by decide
  rcases family_descends (prefixWord ++ tailWord_836512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836513 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 3, 4]
def baseStart_836513 : Nat := 118140960795 + 836513 * 2 ^ 59
def prefixEnd_836513 : Nat := 4983230072969 + 3 ^ 40 * 836513 * 2
def baseEnd_836513 : Nat := 143177747578196957580151

theorem tailTrace_836513 : CollatzResearch.WordTrace tailWord_836513 prefixEnd_836513 143177747578196957580151 := by
  unfold tailWord_836513
  simp only [CollatzResearch.WordTrace]
  refine ⟨30510135618463740891442193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20340090412309160594294795 30510135618463740891442193)
  ·
    refine ⟨22882601713847805668581645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30510135618463740891442193 22882601713847805668581645)
    ·
      refine ⟨8580975642692927125718117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22882601713847805668581645 8580975642692927125718117)
      ·
        refine ⟨1608932933004923836072147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8580975642692927125718117 1608932933004923836072147)
        ·
          refine ⟨2413399399507385754108221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1608932933004923836072147 2413399399507385754108221)
          ·
            refine ⟨905024774815269657790583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2413399399507385754108221 905024774815269657790583)
            ·
              refine ⟨1357537162222904486685875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905024774815269657790583 1357537162222904486685875)
              ·
                refine ⟨2036305743334356730028813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357537162222904486685875 2036305743334356730028813)
                ·
                  refine ⟨763614653750383773760805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2036305743334356730028813 763614653750383773760805)
                  ·
                    refine ⟨143177747578196957580151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 763614653750383773760805 143177747578196957580151)
                    ·
                      rfl

theorem cell23_836513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_836513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836513 prefixEnd_836513 := by exact prefixLift 836513
  have htrace : WordTrace (prefixWord ++ tailWord_836513) baseStart_836513 baseEnd_836513 := by
    simpa [prefixWord, tailWord_836513, baseEnd_836513] using wordTrace_append hprefix tailTrace_836513
  have hstable : (prefixWord ++ tailWord_836513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836513).length < 2 ^ (prefixWord ++ tailWord_836513).sum := by decide
  have hdescent : baseEnd_836513 < baseStart_836513 := by decide
  rcases family_descends (prefixWord ++ tailWord_836513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836570 : List Nat := [3, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3]
def baseStart_836570 : Nat := 118140960795 + 836570 * 2 ^ 59
def prefixEnd_836570 : Nat := 4983230072969 + 3 ^ 40 * 836570 * 2
def baseEnd_836570 : Nat := 429562511131897149727691

theorem tailTrace_836570 : CollatzResearch.WordTrace tailWord_836570 prefixEnd_836570 429562511131897149727691 := by
  unfold tailWord_836570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628053644814309906566791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20341476386171493084178109 7628053644814309906566791)
  ·
    refine ⟨11442080467221464859850187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7628053644814309906566791 11442080467221464859850187)
    ·
      refine ⟨17163120700832197289775281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11442080467221464859850187 17163120700832197289775281)
      ·
        refine ⟨12872340525624147967331461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17163120700832197289775281 12872340525624147967331461)
        ·
          refine ⟨2413563848554527743874649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12872340525624147967331461 2413563848554527743874649)
          ·
            refine ⟨1810172886415895807905987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2413563848554527743874649 1810172886415895807905987)
            ·
              refine ⟨2715259329623843711858981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810172886415895807905987 2715259329623843711858981)
              ·
                refine ⟨509111124304470695973559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2715259329623843711858981 509111124304470695973559)
                ·
                  refine ⟨763666686456706043960339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509111124304470695973559 763666686456706043960339)
                  ·
                    refine ⟨1145500029685059065940509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 763666686456706043960339 1145500029685059065940509)
                    ·
                      refine ⟨429562511131897149727691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1145500029685059065940509 429562511131897149727691)
                      ·
                        rfl

theorem cell23_836570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_836570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836570 prefixEnd_836570 := by exact prefixLift 836570
  have htrace : WordTrace (prefixWord ++ tailWord_836570) baseStart_836570 baseEnd_836570 := by
    simpa [prefixWord, tailWord_836570, baseEnd_836570] using wordTrace_append hprefix tailTrace_836570
  have hstable : (prefixWord ++ tailWord_836570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836570).length < 2 ^ (prefixWord ++ tailWord_836570).sum := by decide
  have hdescent : baseEnd_836570 < baseStart_836570 := by decide
  rcases family_descends (prefixWord ++ tailWord_836570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836579 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 5]
def baseStart_836579 : Nat := 118140960795 + 836579 * 2 ^ 59
def prefixEnd_836579 : Nat := 4983230072969 + 3 ^ 40 * 836579 * 2
def baseEnd_836579 : Nat := 429567132457787614515149

theorem tailTrace_836579 : CollatzResearch.WordTrace tailWord_836579 prefixEnd_836579 429567132457787614515149 := by
  unfold tailWord_836579
  simp only [CollatzResearch.WordTrace]
  refine ⟨30512542836224634163344791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20341695224149756108896527 30512542836224634163344791)
  ·
    refine ⟨45768814254336951245017187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30512542836224634163344791 45768814254336951245017187)
    ·
      refine ⟨68653221381505426867525781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45768814254336951245017187 68653221381505426867525781)
      ·
        refine ⟨3218119752258066884415271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68653221381505426867525781 3218119752258066884415271)
        ·
          refine ⟨4827179628387100326622907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3218119752258066884415271 4827179628387100326622907)
          ·
            refine ⟨7240769442580650489934361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827179628387100326622907 7240769442580650489934361)
            ·
              refine ⟨5430577081935487867450771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7240769442580650489934361 5430577081935487867450771)
              ·
                refine ⟨8145865622903231801176157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430577081935487867450771 8145865622903231801176157)
                ·
                  refine ⟨3054699608588711925441059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8145865622903231801176157 3054699608588711925441059)
                  ·
                    refine ⟨4582049412883067888161589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3054699608588711925441059 4582049412883067888161589)
                    ·
                      refine ⟨429567132457787614515149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4582049412883067888161589 429567132457787614515149)
                      ·
                        rfl

theorem cell23_836579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_836579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836579 prefixEnd_836579 := by exact prefixLift 836579
  have htrace : WordTrace (prefixWord ++ tailWord_836579) baseStart_836579 baseEnd_836579 := by
    simpa [prefixWord, tailWord_836579, baseEnd_836579] using wordTrace_append hprefix tailTrace_836579
  have hstable : (prefixWord ++ tailWord_836579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836579).length < 2 ^ (prefixWord ++ tailWord_836579).sum := by decide
  have hdescent : baseEnd_836579 < baseStart_836579 := by decide
  rcases family_descends (prefixWord ++ tailWord_836579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836586 : List Nat := [3, 1, 3, 1, 2, 3, 2, 1, 1, 6]
def baseStart_836586 : Nat := 118140960795 + 836586 * 2 ^ 59
def prefixEnd_836586 : Nat := 4983230072969 + 3 ^ 40 * 836586 * 2
def baseEnd_836586 : Nat := 143190242274123029042539

theorem tailTrace_836586 : CollatzResearch.WordTrace tailWord_836586 prefixEnd_836586 143190242274123029042539 := by
  unfold tailWord_836586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628199536799818589712403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20341865431466182905899741 7628199536799818589712403)
  ·
    refine ⟨11442299305199727884568605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7628199536799818589712403 11442299305199727884568605)
    ·
      refine ⟨4290862239449897956713227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11442299305199727884568605 4290862239449897956713227)
      ·
        refine ⟨6436293359174846935069841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4290862239449897956713227 6436293359174846935069841)
        ·
          refine ⟨4827220019381135201302381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6436293359174846935069841 4827220019381135201302381)
          ·
            refine ⟨1810207507267925700488393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4827220019381135201302381 1810207507267925700488393)
            ·
              refine ⟨1357655630450944275366295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1810207507267925700488393 1357655630450944275366295)
              ·
                refine ⟨2036483445676416413049443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357655630450944275366295 2036483445676416413049443)
                ·
                  refine ⟨3054725168514624619574165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036483445676416413049443 3054725168514624619574165)
                  ·
                    refine ⟨143190242274123029042539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3054725168514624619574165 143190242274123029042539)
                    ·
                      rfl

theorem cell23_836586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_836586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836586 prefixEnd_836586 := by exact prefixLift 836586
  have htrace : WordTrace (prefixWord ++ tailWord_836586) baseStart_836586 baseEnd_836586 := by
    simpa [prefixWord, tailWord_836586, baseEnd_836586] using wordTrace_append hprefix tailTrace_836586
  have hstable : (prefixWord ++ tailWord_836586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836586).length < 2 ^ (prefixWord ++ tailWord_836586).sum := by decide
  have hdescent : baseEnd_836586 < baseStart_836586 := by decide
  rcases family_descends (prefixWord ++ tailWord_836586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836593 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 5, 2, 2]
def baseStart_836593 : Nat := 118140960795 + 836593 * 2 ^ 59
def prefixEnd_836593 : Nat := 4983230072969 + 3 ^ 40 * 836593 * 2
def baseEnd_836593 : Nat := 429574321186950559740085

theorem tailTrace_836593 : CollatzResearch.WordTrace tailWord_836593 prefixEnd_836593 429574321186950559740085 := by
  unfold tailWord_836593
  simp only [CollatzResearch.WordTrace]
  refine ⟨30513053458173914554354433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20342035638782609702902955 30513053458173914554354433)
  ·
    refine ⟨22884790093630435915765825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30513053458173914554354433 22884790093630435915765825)
    ·
      refine ⟨17163592570222826936824369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22884790093630435915765825 17163592570222826936824369)
      ·
        refine ⟨12872694427667120202618277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17163592570222826936824369 12872694427667120202618277)
        ·
          refine ⟨2413630205187585037990927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12872694427667120202618277 2413630205187585037990927)
          ·
            refine ⟨3620445307781377556986391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413630205187585037990927 3620445307781377556986391)
            ·
              refine ⟨5430667961672066335479587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3620445307781377556986391 5430667961672066335479587)
              ·
                refine ⟨8146001942508099503219381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430667961672066335479587 8146001942508099503219381)
                ·
                  refine ⟨763687682110134328426817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8146001942508099503219381 763687682110134328426817)
                  ·
                    refine ⟨572765761582600746320113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 763687682110134328426817 572765761582600746320113)
                    ·
                      refine ⟨429574321186950559740085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 572765761582600746320113 429574321186950559740085)
                      ·
                        rfl

theorem cell23_836593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_836593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836593 prefixEnd_836593 := by exact prefixLift 836593
  have htrace : WordTrace (prefixWord ++ tailWord_836593) baseStart_836593 baseEnd_836593 := by
    simpa [prefixWord, tailWord_836593, baseEnd_836593] using wordTrace_append hprefix tailTrace_836593
  have hstable : (prefixWord ++ tailWord_836593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836593).length < 2 ^ (prefixWord ++ tailWord_836593).sum := by decide
  have hdescent : baseEnd_836593 < baseStart_836593 := by decide
  rcases family_descends (prefixWord ++ tailWord_836593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836640 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 1, 2, 4]
def baseStart_836640 : Nat := 118140960795 + 836640 * 2 ^ 59
def prefixEnd_836640 : Nat := 4983230072969 + 3 ^ 40 * 836640 * 2
def baseEnd_836640 : Nat := 429598454777711875852369

theorem tailTrace_836640 : CollatzResearch.WordTrace tailWord_836640 prefixEnd_836640 429598454777711875852369 := by
  unfold tailWord_836640
  simp only [CollatzResearch.WordTrace]
  refine ⟨15257383844501820790657687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20343178459335761054210249 15257383844501820790657687)
  ·
    refine ⟨22886075766752731185986531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15257383844501820790657687 22886075766752731185986531)
    ·
      refine ⟨34329113650129096778979797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22886075766752731185986531 34329113650129096778979797)
      ·
        refine ⟨804588601174900705757339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 34329113650129096778979797 804588601174900705757339)
        ·
          refine ⟨1206882901762351058636009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804588601174900705757339 1206882901762351058636009)
          ·
            refine ⟨905162176321763293977007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206882901762351058636009 905162176321763293977007)
            ·
              refine ⟨1357743264482644940965511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905162176321763293977007 1357743264482644940965511)
              ·
                refine ⟨2036614896723967411448267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357743264482644940965511 2036614896723967411448267)
                ·
                  refine ⟨3054922345085951117172401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036614896723967411448267 3054922345085951117172401)
                  ·
                    refine ⟨2291191758814463337879301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3054922345085951117172401 2291191758814463337879301)
                    ·
                      refine ⟨429598454777711875852369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2291191758814463337879301 429598454777711875852369)
                      ·
                        rfl

theorem cell23_836640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_836640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836640 prefixEnd_836640 := by exact prefixLift 836640
  have htrace : WordTrace (prefixWord ++ tailWord_836640) baseStart_836640 baseEnd_836640 := by
    simpa [prefixWord, tailWord_836640, baseEnd_836640] using wordTrace_append hprefix tailTrace_836640
  have hstable : (prefixWord ++ tailWord_836640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836640).length < 2 ^ (prefixWord ++ tailWord_836640).sum := by decide
  have hdescent : baseEnd_836640 < baseStart_836640 := by decide
  rcases family_descends (prefixWord ++ tailWord_836640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836643 : List Nat := [1, 1, 1, 4, 3, 4, 1, 1, 1, 3, 3]
def baseStart_836643 : Nat := 118140960795 + 836643 * 2 ^ 59
def prefixEnd_836643 : Nat := 4983230072969 + 3 ^ 40 * 836643 * 2
def baseEnd_836643 : Nat := 429599995219675364114855

theorem tailTrace_836643 : CollatzResearch.WordTrace tailWord_836643 prefixEnd_836643 429599995219675364114855 := by
  unfold tailWord_836643
  simp only [CollatzResearch.WordTrace]
  refine ⟨30514877107992773093674583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20343251405328515395783055 30514877107992773093674583)
  ·
    refine ⟨45772315661989159640511875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30514877107992773093674583 45772315661989159640511875)
    ·
      refine ⟨68658473492983739460767813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45772315661989159640511875 68658473492983739460767813)
      ·
        refine ⟨12873463779934451148893965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68658473492983739460767813 12873463779934451148893965)
        ·
          refine ⟨4827548917475419180835237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12873463779934451148893965 4827548917475419180835237)
          ·
            refine ⟨905165422026641096406607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4827548917475419180835237 905165422026641096406607)
            ·
              refine ⟨1357748133039961644609911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905165422026641096406607 1357748133039961644609911)
              ·
                refine ⟨2036622199559942466914867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357748133039961644609911 2036622199559942466914867)
                ·
                  refine ⟨3054933299339913700372301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036622199559942466914867 3054933299339913700372301)
                  ·
                    refine ⟨1145599987252467637639613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3054933299339913700372301 1145599987252467637639613)
                    ·
                      refine ⟨429599995219675364114855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1145599987252467637639613 429599995219675364114855)
                      ·
                        rfl

theorem cell23_836643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_836643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836643 prefixEnd_836643 := by exact prefixLift 836643
  have htrace : WordTrace (prefixWord ++ tailWord_836643) baseStart_836643 baseEnd_836643 := by
    simpa [prefixWord, tailWord_836643, baseEnd_836643] using wordTrace_append hprefix tailTrace_836643
  have hstable : (prefixWord ++ tailWord_836643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836643).length < 2 ^ (prefixWord ++ tailWord_836643).sum := by decide
  have hdescent : baseEnd_836643 < baseStart_836643 := by decide
  rcases family_descends (prefixWord ++ tailWord_836643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836650 : List Nat := [3, 1, 4, 1, 4, 1, 2, 7]
def baseStart_836650 : Nat := 118140960795 + 836650 * 2 ^ 59
def prefixEnd_836650 : Nat := 4983230072969 + 3 ^ 40 * 836650 * 2
def baseEnd_836650 : Nat := 15911244058676179138049

theorem tailTrace_836650 : CollatzResearch.WordTrace tailWord_836650 prefixEnd_836650 15911244058676179138049 := by
  unfold tailWord_836650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628783104741853322294851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20343421612644942192786269 7628783104741853322294851)
  ·
    refine ⟨11443174657112779983442277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7628783104741853322294851 11443174657112779983442277)
    ·
      refine ⟨2145595248208646246895427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11443174657112779983442277 2145595248208646246895427)
      ·
        refine ⟨3218392872312969370343141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145595248208646246895427 3218392872312969370343141)
        ·
          refine ⟨603448663558681756939339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3218392872312969370343141 603448663558681756939339)
          ·
            refine ⟨905172995338022635409009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603448663558681756939339 905172995338022635409009)
            ·
              refine ⟨678879746503516976556757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905172995338022635409009 678879746503516976556757)
              ·
                refine ⟨15911244058676179138049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 678879746503516976556757 15911244058676179138049)
                ·
                  rfl

theorem cell23_836650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 2, 7].length) (baseStart_836650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836650 prefixEnd_836650 := by exact prefixLift 836650
  have htrace : WordTrace (prefixWord ++ tailWord_836650) baseStart_836650 baseEnd_836650 := by
    simpa [prefixWord, tailWord_836650, baseEnd_836650] using wordTrace_append hprefix tailTrace_836650
  have hstable : (prefixWord ++ tailWord_836650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836650).length < 2 ^ (prefixWord ++ tailWord_836650).sum := by decide
  have hdescent : baseEnd_836650 < baseStart_836650 := by decide
  rcases family_descends (prefixWord ++ tailWord_836650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836660 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_836660 : Nat := 118140960795 + 836660 * 2 ^ 59
def prefixEnd_836660 : Nat := 4983230072969 + 3 ^ 40 * 836660 * 2
def baseEnd_836660 : Nat := 429608724390801797602277

theorem tailTrace_836660 : CollatzResearch.WordTrace tailWord_836660 prefixEnd_836660 429608724390801797602277 := by
  unfold tailWord_836660
  simp only [CollatzResearch.WordTrace]
  refine ⟨15257748574465592498521717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20343664765954123331362289 15257748574465592498521717)
  ·
    refine ⟨1430413928856149296736411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15257748574465592498521717 1430413928856149296736411)
    ·
      refine ⟨2145620893284223945104617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1430413928856149296736411 2145620893284223945104617)
      ·
        refine ⟨1609215669963167958828463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2145620893284223945104617 1609215669963167958828463)
        ·
          refine ⟨2413823504944751938242695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609215669963167958828463 2413823504944751938242695)
          ·
            refine ⟨3620735257417127907364043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413823504944751938242695 3620735257417127907364043)
            ·
              refine ⟨5431102886125691861046065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3620735257417127907364043 5431102886125691861046065)
              ·
                refine ⟨4073327164594268895784549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5431102886125691861046065 4073327164594268895784549)
                ·
                  refine ⟨763748843361425417959603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4073327164594268895784549 763748843361425417959603)
                  ·
                    refine ⟨1145623265042138126939405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 763748843361425417959603 1145623265042138126939405)
                    ·
                      refine ⟨429608724390801797602277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1145623265042138126939405 429608724390801797602277)
                      ·
                        rfl

theorem cell23_836660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_836660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836660 prefixEnd_836660 := by exact prefixLift 836660
  have htrace : WordTrace (prefixWord ++ tailWord_836660) baseStart_836660 baseEnd_836660 := by
    simpa [prefixWord, tailWord_836660, baseEnd_836660] using wordTrace_append hprefix tailTrace_836660
  have hstable : (prefixWord ++ tailWord_836660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836660).length < 2 ^ (prefixWord ++ tailWord_836660).sum := by decide
  have hdescent : baseEnd_836660 < baseStart_836660 := by decide
  rcases family_descends (prefixWord ++ tailWord_836660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836686 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_836686 : Nat := 118140960795 + 836686 * 2 ^ 59
def prefixEnd_836686 : Nat := 4983230072969 + 3 ^ 40 * 836686 * 2
def baseEnd_836686 : Nat := 429622074887818695877157

theorem tailTrace_836686 : CollatzResearch.WordTrace tailWord_836686 prefixEnd_836686 429622074887818695877157 := by
  unfold tailWord_836686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3814555680854623929686239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20344296964557994291659941 3814555680854623929686239)
  ·
    refine ⟨5721833521281935894529359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3814555680854623929686239 5721833521281935894529359)
    ·
      refine ⟨8582750281922903841794039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5721833521281935894529359 8582750281922903841794039)
      ·
        refine ⟨12874125422884355762691059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8582750281922903841794039 12874125422884355762691059)
        ·
          refine ⟨19311188134326533644036589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12874125422884355762691059 19311188134326533644036589)
          ·
            refine ⟨7241695550372450116513721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19311188134326533644036589 7241695550372450116513721)
            ·
              refine ⟨5431271662779337587385291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7241695550372450116513721 5431271662779337587385291)
              ·
                refine ⟨8146907494169006381077937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5431271662779337587385291 8146907494169006381077937)
                ·
                  refine ⟨6110180620626754785808453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8146907494169006381077937 6110180620626754785808453)
                  ·
                    refine ⟨1145658866367516522339085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6110180620626754785808453 1145658866367516522339085)
                    ·
                      refine ⟨429622074887818695877157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1145658866367516522339085 429622074887818695877157)
                      ·
                        rfl

theorem cell23_836686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_836686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836686 prefixEnd_836686 := by exact prefixLift 836686
  have htrace : WordTrace (prefixWord ++ tailWord_836686) baseStart_836686 baseEnd_836686 := by
    simpa [prefixWord, tailWord_836686, baseEnd_836686] using wordTrace_append hprefix tailTrace_836686
  have hstable : (prefixWord ++ tailWord_836686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836686).length < 2 ^ (prefixWord ++ tailWord_836686).sum := by decide
  have hdescent : baseEnd_836686 < baseStart_836686 := by decide
  rcases family_descends (prefixWord ++ tailWord_836686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836694 : List Nat := [5, 2, 2, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_836694 : Nat := 118140960795 + 836694 * 2 ^ 59
def prefixEnd_836694 : Nat := 4983230072969 + 3 ^ 40 * 836694 * 2
def baseEnd_836694 : Nat := 429626182733054664577121

theorem tailTrace_836694 : CollatzResearch.WordTrace tailWord_836694 prefixEnd_836694 429626182733054664577121 := by
  unfold tailWord_836694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1907296076925500550236321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20344491487205339202520757 1907296076925500550236321)
  ·
    refine ⟨1430472057694125412677241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1907296076925500550236321 1430472057694125412677241)
    ·
      refine ⟨1072854043270594059507931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1430472057694125412677241 1072854043270594059507931)
      ·
        refine ⟨1609281064905891089261897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072854043270594059507931 1609281064905891089261897)
        ·
          refine ⟨1206960798679418316946423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1609281064905891089261897 1206960798679418316946423)
          ·
            refine ⟨1810441198019127475419635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206960798679418316946423 1810441198019127475419635)
            ·
              refine ⟨2715661797028691213129453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810441198019127475419635 2715661797028691213129453)
              ·
                refine ⟨1018373173885759204923545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2715661797028691213129453 1018373173885759204923545)
                ·
                  refine ⟨763779880414319403692659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1018373173885759204923545 763779880414319403692659)
                  ·
                    refine ⟨1145669820621479105538989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 763779880414319403692659 1145669820621479105538989)
                    ·
                      refine ⟨429626182733054664577121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1145669820621479105538989 429626182733054664577121)
                      ·
                        rfl

theorem cell23_836694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_836694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836694 prefixEnd_836694 := by exact prefixLift 836694
  have htrace : WordTrace (prefixWord ++ tailWord_836694) baseStart_836694 baseEnd_836694 := by
    simpa [prefixWord, tailWord_836694, baseEnd_836694] using wordTrace_append hprefix tailTrace_836694
  have hstable : (prefixWord ++ tailWord_836694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836694).length < 2 ^ (prefixWord ++ tailWord_836694).sum := by decide
  have hdescent : baseEnd_836694 < baseStart_836694 := by decide
  rcases family_descends (prefixWord ++ tailWord_836694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836736 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 2, 5]
def baseStart_836736 : Nat := 118140960795 + 836736 * 2 ^ 59
def prefixEnd_836736 : Nat := 4983230072969 + 3 ^ 40 * 836736 * 2
def baseEnd_836736 : Nat := 143215916306847833417309

theorem tailTrace_836736 : CollatzResearch.WordTrace tailWord_836736 prefixEnd_836736 143215916306847833417309 := by
  unfold tailWord_836736
  simp only [CollatzResearch.WordTrace]
  refine ⟨15259134548327924988405031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20345512731103899984540041 15259134548327924988405031)
  ·
    refine ⟨22888701822491887482607547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15259134548327924988405031 22888701822491887482607547)
    ·
      refine ⟨34333052733737831223911321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22888701822491887482607547 34333052733737831223911321)
      ·
        refine ⟨25749789550303373417933491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34333052733737831223911321 25749789550303373417933491)
        ·
          refine ⟨38624684325455060126900237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25749789550303373417933491 38624684325455060126900237)
          ·
            refine ⟨14484256622045647547587589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38624684325455060126900237 14484256622045647547587589)
            ·
              refine ⟨2715798116633558915172673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14484256622045647547587589 2715798116633558915172673)
              ·
                refine ⟨2036848587475169186379505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2715798116633558915172673 2036848587475169186379505)
                ·
                  refine ⟨1527636440606376889784629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2036848587475169186379505 1527636440606376889784629)
                  ·
                    refine ⟨143215916306847833417309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1527636440606376889784629 143215916306847833417309)
                    ·
                      rfl

theorem cell23_836736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 2, 5].length) (baseStart_836736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836736 prefixEnd_836736 := by exact prefixLift 836736
  have htrace : WordTrace (prefixWord ++ tailWord_836736) baseStart_836736 baseEnd_836736 := by
    simpa [prefixWord, tailWord_836736, baseEnd_836736] using wordTrace_append hprefix tailTrace_836736
  have hstable : (prefixWord ++ tailWord_836736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836736).length < 2 ^ (prefixWord ++ tailWord_836736).sum := by decide
  have hdescent : baseEnd_836736 < baseStart_836736 := by decide
  rcases family_descends (prefixWord ++ tailWord_836736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836740 : List Nat := [2, 3, 2, 1, 2, 2, 4, 2, 5]
def baseStart_836740 : Nat := 118140960795 + 836740 * 2 ^ 59
def prefixEnd_836740 : Nat := 4983230072969 + 3 ^ 40 * 836740 * 2
def baseEnd_836740 : Nat := 47738866982573498289101

theorem tailTrace_836740 : CollatzResearch.WordTrace tailWord_836740 prefixEnd_836740 47738866982573498289101 := by
  unfold tailWord_836740
  simp only [CollatzResearch.WordTrace]
  refine ⟨15259207494320679329977837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20345609992427572439970449 15259207494320679329977837)
  ·
    refine ⟨5722202810370254748741689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15259207494320679329977837 5722202810370254748741689)
    ·
      refine ⟨4291652107777691061556267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5722202810370254748741689 4291652107777691061556267)
      ·
        refine ⟨6437478161666536592334401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4291652107777691061556267 6437478161666536592334401)
        ·
          refine ⟨4828108621249902444250801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6437478161666536592334401 4828108621249902444250801)
          ·
            refine ⟨3621081465937426833188101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4828108621249902444250801 3621081465937426833188101)
            ·
              refine ⟨678952774863267531222769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3621081465937426833188101 678952774863267531222769)
              ·
                refine ⟨509214581147450648417077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678952774863267531222769 509214581147450648417077)
                ·
                  refine ⟨47738866982573498289101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 509214581147450648417077 47738866982573498289101)
                  ·
                    rfl

theorem cell23_836740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_836740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836740 prefixEnd_836740 := by exact prefixLift 836740
  have htrace : WordTrace (prefixWord ++ tailWord_836740) baseStart_836740 baseEnd_836740 := by
    simpa [prefixWord, tailWord_836740, baseEnd_836740] using wordTrace_append hprefix tailTrace_836740
  have hstable : (prefixWord ++ tailWord_836740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836740).length < 2 ^ (prefixWord ++ tailWord_836740).sum := by decide
  have hdescent : baseEnd_836740 < baseStart_836740 := by decide
  rcases family_descends (prefixWord ++ tailWord_836740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836746 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_836746 : Nat := 118140960795 + 836746 * 2 ^ 59
def prefixEnd_836746 : Nat := 4983230072969 + 3 ^ 40 * 836746 * 2
def baseEnd_836746 : Nat := 429652883727088461126881

theorem tailTrace_836746 : CollatzResearch.WordTrace tailWord_836746 prefixEnd_836746 429652883727088461126881 := by
  unfold tailWord_836746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7629658456654905421168523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20345755884413081123116061 7629658456654905421168523)
  ·
    refine ⟨11444487684982358131752785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7629658456654905421168523 11444487684982358131752785)
    ·
      refine ⟨8583365763736768598814589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11444487684982358131752785 8583365763736768598814589)
      ·
        refine ⟨3218762161401288224555471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8583365763736768598814589 3218762161401288224555471)
        ·
          refine ⟨4828143242101932336833207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3218762161401288224555471 4828143242101932336833207)
          ·
            refine ⟨7242214863152898505249811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4828143242101932336833207 7242214863152898505249811)
            ·
              refine ⟨10863322294729347757874717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7242214863152898505249811 10863322294729347757874717)
              ·
                refine ⟨4073745860523505409203019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10863322294729347757874717 4073745860523505409203019)
                ·
                  refine ⟨6110618790785258113804529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4073745860523505409203019 6110618790785258113804529)
                  ·
                    refine ⟨4582964093088943585353397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6110618790785258113804529 4582964093088943585353397)
                    ·
                      refine ⟨429652883727088461126881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4582964093088943585353397 429652883727088461126881)
                      ·
                        rfl

theorem cell23_836746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_836746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836746 prefixEnd_836746 := by exact prefixLift 836746
  have htrace : WordTrace (prefixWord ++ tailWord_836746) baseStart_836746 baseEnd_836746 := by
    simpa [prefixWord, tailWord_836746, baseEnd_836746] using wordTrace_append hprefix tailTrace_836746
  have hstable : (prefixWord ++ tailWord_836746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836746).length < 2 ^ (prefixWord ++ tailWord_836746).sum := by decide
  have hdescent : baseEnd_836746 < baseStart_836746 := by decide
  rcases family_descends (prefixWord ++ tailWord_836746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836773 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 2, 1, 4]
def baseStart_836773 : Nat := 118140960795 + 836773 * 2 ^ 59
def prefixEnd_836773 : Nat := 4983230072969 + 3 ^ 40 * 836773 * 2
def baseEnd_836773 : Nat := 429666747704759855489257

theorem tailTrace_836773 : CollatzResearch.WordTrace tailWord_836773 prefixEnd_836773 429666747704759855489257 := by
  unfold tailWord_836773
  simp only [CollatzResearch.WordTrace]
  refine ⟨30519618597521805295906973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20346412398347870197271315 30519618597521805295906973)
  ·
    refine ⟨11444856974070676985965115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30519618597521805295906973 11444856974070676985965115)
    ·
      refine ⟨17167285461106015478947673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11444856974070676985965115 17167285461106015478947673)
      ·
        refine ⟨12875464095829511609210755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17167285461106015478947673 12875464095829511609210755)
        ·
          refine ⟨19313196143744267413816133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12875464095829511609210755 19313196143744267413816133)
          ·
            refine ⟨3621224276952050140090525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19313196143744267413816133 3621224276952050140090525)
            ·
              refine ⟨1357959103857018802533947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3621224276952050140090525 1357959103857018802533947)
              ·
                refine ⟨2036938655785528203800921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357959103857018802533947 2036938655785528203800921)
                ·
                  refine ⟨1527703991839146152850691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2036938655785528203800921 1527703991839146152850691)
                  ·
                    refine ⟨2291555987758719229276037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1527703991839146152850691 2291555987758719229276037)
                    ·
                      refine ⟨429666747704759855489257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2291555987758719229276037 429666747704759855489257)
                      ·
                        rfl

theorem cell23_836773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_836773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836773 prefixEnd_836773 := by exact prefixLift 836773
  have htrace : WordTrace (prefixWord ++ tailWord_836773) baseStart_836773 baseEnd_836773 := by
    simpa [prefixWord, tailWord_836773, baseEnd_836773] using wordTrace_append hprefix tailTrace_836773
  have hstable : (prefixWord ++ tailWord_836773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836773).length < 2 ^ (prefixWord ++ tailWord_836773).sum := by decide
  have hdescent : baseEnd_836773 < baseStart_836773 := by decide
  rcases family_descends (prefixWord ++ tailWord_836773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836786 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_836786 : Nat := 118140960795 + 836786 * 2 ^ 59
def prefixEnd_836786 : Nat := 4983230072969 + 3 ^ 40 * 836786 * 2
def baseEnd_836786 : Nat := 429673422953268304626697

theorem tailTrace_836786 : CollatzResearch.WordTrace tailWord_836786 prefixEnd_836786 429673422953268304626697 := by
  unfold tailWord_836786
  simp only [CollatzResearch.WordTrace]
  refine ⟨7630023186618677129032553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20346728497649805677420141 7630023186618677129032553)
  ·
    refine ⟨5722517389964007846774415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7630023186618677129032553 5722517389964007846774415)
    ·
      refine ⟨8583776084946011770161623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5722517389964007846774415 8583776084946011770161623)
      ·
        refine ⟨12875664127419017655242435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8583776084946011770161623 12875664127419017655242435)
        ·
          refine ⟨19313496191128526482863653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12875664127419017655242435 19313496191128526482863653)
          ·
            refine ⟨3621280535836598715536935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19313496191128526482863653 3621280535836598715536935)
            ·
              refine ⟨5431920803754898073305403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3621280535836598715536935 5431920803754898073305403)
              ·
                refine ⟨8147881205632347109958105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5431920803754898073305403 8147881205632347109958105)
                ·
                  refine ⟨6110910904224260332468579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8147881205632347109958105 6110910904224260332468579)
                  ·
                    refine ⟨9166366356336390498702869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6110910904224260332468579 9166366356336390498702869)
                    ·
                      refine ⟨429673422953268304626697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9166366356336390498702869 429673422953268304626697)
                      ·
                        rfl

theorem cell23_836786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_836786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836786 prefixEnd_836786 := by exact prefixLift 836786
  have htrace : WordTrace (prefixWord ++ tailWord_836786) baseStart_836786 baseEnd_836786 := by
    simpa [prefixWord, tailWord_836786, baseEnd_836786] using wordTrace_append hprefix tailTrace_836786
  have hstable : (prefixWord ++ tailWord_836786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836786).length < 2 ^ (prefixWord ++ tailWord_836786).sum := by decide
  have hdescent : baseEnd_836786 < baseStart_836786 := by decide
  rcases family_descends (prefixWord ++ tailWord_836786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836800 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 3, 4]
def baseStart_836800 : Nat := 118140960795 + 836800 * 2 ^ 59
def prefixEnd_836800 : Nat := 4983230072969 + 3 ^ 40 * 836800 * 2
def baseEnd_836800 : Nat := 143226870560810416617211

theorem tailTrace_836800 : CollatzResearch.WordTrace tailWord_836800 prefixEnd_836800 143226870560810416617211 := by
  unfold tailWord_836800
  simp only [CollatzResearch.WordTrace]
  refine ⟨15260301684211994453569927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20347068912282659271426569 15260301684211994453569927)
  ·
    refine ⟨22890452526317991680354891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15260301684211994453569927 22890452526317991680354891)
    ·
      refine ⟨34335678789476987520532337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22890452526317991680354891 34335678789476987520532337)
      ·
        refine ⟨25751759092107740640399253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34335678789476987520532337 25751759092107740640399253)
        ·
          refine ⟨1207113707442550342518715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25751759092107740640399253 1207113707442550342518715)
          ·
            refine ⟨1810670561163825513778073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207113707442550342518715 1810670561163825513778073)
            ·
              refine ⟨1358002920872869135333555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1810670561163825513778073 1358002920872869135333555)
              ·
                refine ⟨2037004381309303703000333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358002920872869135333555 2037004381309303703000333)
                ·
                  refine ⟨763876642990988888625125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2037004381309303703000333 763876642990988888625125)
                  ·
                    refine ⟨143226870560810416617211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 763876642990988888625125 143226870560810416617211)
                    ·
                      rfl

theorem cell23_836800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 3, 4].length) (baseStart_836800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836800 prefixEnd_836800 := by exact prefixLift 836800
  have htrace : WordTrace (prefixWord ++ tailWord_836800) baseStart_836800 baseEnd_836800 := by
    simpa [prefixWord, tailWord_836800, baseEnd_836800] using wordTrace_append hprefix tailTrace_836800
  have hstable : (prefixWord ++ tailWord_836800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836800).length < 2 ^ (prefixWord ++ tailWord_836800).sum := by decide
  have hdescent : baseEnd_836800 < baseStart_836800 := by decide
  rcases family_descends (prefixWord ++ tailWord_836800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836843 : List Nat := [1, 1, 1, 1, 2, 6, 2, 3, 1, 5]
def baseStart_836843 : Nat := 118140960795 + 836843 * 2 ^ 59
def prefixEnd_836843 : Nat := 4983230072969 + 3 ^ 40 * 836843 * 2
def baseEnd_836843 : Nat := 143234230450191527204645

theorem tailTrace_836843 : CollatzResearch.WordTrace tailWord_836843 prefixEnd_836843 143234230450191527204645 := by
  unfold tailWord_836843
  simp only [CollatzResearch.WordTrace]
  refine ⟨30522171707268207250955183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20348114471512138167303455 30522171707268207250955183)
  ·
    refine ⟨45783257560902310876432775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30522171707268207250955183 45783257560902310876432775)
    ·
      refine ⟨68674886341353466314649163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45783257560902310876432775 68674886341353466314649163)
      ·
        refine ⟨103012329512030199471973745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68674886341353466314649163 103012329512030199471973745)
        ·
          refine ⟨77259247134022649603980309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103012329512030199471973745 77259247134022649603980309)
          ·
            refine ⟨3621527209407311700186577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77259247134022649603980309 3621527209407311700186577)
            ·
              refine ⟨2716145407055483775139933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3621527209407311700186577 2716145407055483775139933)
              ·
                refine ⟨1018554527645806415677475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2716145407055483775139933 1018554527645806415677475)
                ·
                  refine ⟨1527831791468709623516213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018554527645806415677475 1527831791468709623516213)
                  ·
                    refine ⟨143234230450191527204645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1527831791468709623516213 143234230450191527204645)
                    ·
                      rfl

theorem cell23_836843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 5].length) (baseStart_836843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836843 prefixEnd_836843 := by exact prefixLift 836843
  have htrace : WordTrace (prefixWord ++ tailWord_836843) baseStart_836843 baseEnd_836843 := by
    simpa [prefixWord, tailWord_836843, baseEnd_836843] using wordTrace_append hprefix tailTrace_836843
  have hstable : (prefixWord ++ tailWord_836843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836843).length < 2 ^ (prefixWord ++ tailWord_836843).sum := by decide
  have hdescent : baseEnd_836843 < baseStart_836843 := by decide
  rcases family_descends (prefixWord ++ tailWord_836843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836903 : List Nat := [1, 1, 8, 13]
def baseStart_836903 : Nat := 118140960795 + 836903 * 2 ^ 59
def prefixEnd_836903 : Nat := 4983230072969 + 3 ^ 40 * 836903 * 2
def baseEnd_836903 : Nat := 196494513118355897057

theorem tailTrace_836903 : CollatzResearch.WordTrace tailWord_836903 prefixEnd_836903 196494513118355897057 := by
  unfold tailWord_836903
  simp only [CollatzResearch.WordTrace]
  refine ⟨30524360087050837498139363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20349573391367224998759575 30524360087050837498139363)
  ·
    refine ⟨45786540130576256247209045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30524360087050837498139363 45786540130576256247209045)
    ·
      refine ⟨536561017155190502896981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 45786540130576256247209045 536561017155190502896981)
      ·
        refine ⟨196494513118355897057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 536561017155190502896981 196494513118355897057)
        ·
          rfl

theorem cell23_836903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 13].length) (baseStart_836903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836903 prefixEnd_836903 := by exact prefixLift 836903
  have htrace : WordTrace (prefixWord ++ tailWord_836903) baseStart_836903 baseEnd_836903 := by
    simpa [prefixWord, tailWord_836903, baseEnd_836903] using wordTrace_append hprefix tailTrace_836903
  have hstable : (prefixWord ++ tailWord_836903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836903).length < 2 ^ (prefixWord ++ tailWord_836903).sum := by decide
  have hdescent : baseEnd_836903 < baseStart_836903 := by decide
  rcases family_descends (prefixWord ++ tailWord_836903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836963 : List Nat := [1, 1, 1, 5, 2, 2, 1, 2, 2, 6]
def baseStart_836963 : Nat := 118140960795 + 836963 * 2 ^ 59
def prefixEnd_836963 : Nat := 4983230072969 + 3 ^ 40 * 836963 * 2
def baseEnd_836963 : Nat := 143254769676371370704461

theorem tailTrace_836963 : CollatzResearch.WordTrace tailWord_836963 prefixEnd_836963 143254769676371370704461 := by
  unfold tailWord_836963
  simp only [CollatzResearch.WordTrace]
  refine ⟨30526548466833467745323543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20351032311222311830215695 30526548466833467745323543)
  ·
    refine ⟨45789822700250201617985315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30526548466833467745323543 45789822700250201617985315)
    ·
      refine ⟨68684734050375302426977973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45789822700250201617985315 68684734050375302426977973)
      ·
        refine ⟨6439193817222684602529185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68684734050375302426977973 6439193817222684602529185)
        ·
          refine ⟨4829395362917013451896889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6439193817222684602529185 4829395362917013451896889)
          ·
            refine ⟨3622046522187760088922667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4829395362917013451896889 3622046522187760088922667)
            ·
              refine ⟨5433069783281640133384001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3622046522187760088922667 5433069783281640133384001)
              ·
                refine ⟨4074802337461230100038001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5433069783281640133384001 4074802337461230100038001)
                ·
                  refine ⟨3056101753095922575028501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4074802337461230100038001 3056101753095922575028501)
                  ·
                    refine ⟨143254769676371370704461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3056101753095922575028501 143254769676371370704461)
                    ·
                      rfl

theorem cell23_836963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 6].length) (baseStart_836963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836963 prefixEnd_836963 := by exact prefixLift 836963
  have htrace : WordTrace (prefixWord ++ tailWord_836963) baseStart_836963 baseEnd_836963 := by
    simpa [prefixWord, tailWord_836963, baseEnd_836963] using wordTrace_append hprefix tailTrace_836963
  have hstable : (prefixWord ++ tailWord_836963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836963).length < 2 ^ (prefixWord ++ tailWord_836963).sum := by decide
  have hdescent : baseEnd_836963 < baseStart_836963 := by decide
  rcases family_descends (prefixWord ++ tailWord_836963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836964 : List Nat := [2, 3, 1, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_836964 : Nat := 118140960795 + 836964 * 2 ^ 59
def prefixEnd_836964 : Nat := 4983230072969 + 3 ^ 40 * 836964 * 2
def baseEnd_836964 : Nat := 429764822509768608200879

theorem tailTrace_836964 : CollatzResearch.WordTrace tailWord_836964 prefixEnd_836964 429764822509768608200879 := by
  unfold tailWord_836964
  simp only [CollatzResearch.WordTrace]
  refine ⟨15263292469914922458054973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20351056626553229944073297 15263292469914922458054973)
  ·
    refine ⟨5723734676218095921770615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15263292469914922458054973 5723734676218095921770615)
    ·
      refine ⟨8585602014327143882655923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5723734676218095921770615 8585602014327143882655923)
      ·
        refine ⟨12878403021490715823983885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8585602014327143882655923 12878403021490715823983885)
        ·
          refine ⟨4829401133059018433993957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12878403021490715823983885 4829401133059018433993957)
          ·
            refine ⟨905512712448565956373867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4829401133059018433993957 905512712448565956373867)
            ·
              refine ⟨1358269068672848934560801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905512712448565956373867 1358269068672848934560801)
              ·
                refine ⟨1018701801504636700920601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358269068672848934560801 1018701801504636700920601)
                ·
                  refine ⟨764026351128477525690451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1018701801504636700920601 764026351128477525690451)
                  ·
                    refine ⟨1146039526692716288535677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 764026351128477525690451 1146039526692716288535677)
                    ·
                      refine ⟨429764822509768608200879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1146039526692716288535677 429764822509768608200879)
                      ·
                        rfl

theorem cell23_836964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_836964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836964 prefixEnd_836964 := by exact prefixLift 836964
  have htrace : WordTrace (prefixWord ++ tailWord_836964) baseStart_836964 baseEnd_836964 := by
    simpa [prefixWord, tailWord_836964, baseEnd_836964] using wordTrace_append hprefix tailTrace_836964
  have hstable : (prefixWord ++ tailWord_836964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836964).length < 2 ^ (prefixWord ++ tailWord_836964).sum := by decide
  have hdescent : baseEnd_836964 < baseStart_836964 := by decide
  rcases family_descends (prefixWord ++ tailWord_836964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836981 : List Nat := [1, 3, 4, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_836981 : Nat := 118140960795 + 836981 * 2 ^ 59
def prefixEnd_836981 : Nat := 4983230072969 + 3 ^ 40 * 836981 * 2
def baseEnd_836981 : Nat := 429773551680895041688301

theorem tailTrace_836981 : CollatzResearch.WordTrace tailWord_836981 prefixEnd_836981 429773551680895041688301 := by
  unfold tailWord_836981
  simp only [CollatzResearch.WordTrace]
  refine ⟨30527204980768256819478797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20351469987178837879652531 30527204980768256819478797)
  ·
    refine ⟨11447701867788096307304549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30527204980768256819478797 11447701867788096307304549)
    ·
      refine ⟨2146444100210268057619603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11447701867788096307304549 2146444100210268057619603)
      ·
        refine ⟨3219666150315402086429405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2146444100210268057619603 3219666150315402086429405)
        ·
          refine ⟨1207374806368275782411027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3219666150315402086429405 1207374806368275782411027)
          ·
            refine ⟨1811062209552413673616541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207374806368275782411027 1811062209552413673616541)
            ·
              refine ⟨679148328582155127606203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1811062209552413673616541 679148328582155127606203)
              ·
                refine ⟨1018722492873232691409305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679148328582155127606203 1018722492873232691409305)
                ·
                  refine ⟨764041869654924518556979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1018722492873232691409305 764041869654924518556979)
                  ·
                    refine ⟨1146062804482386777835469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 764041869654924518556979 1146062804482386777835469)
                    ·
                      refine ⟨429773551680895041688301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1146062804482386777835469 429773551680895041688301)
                      ·
                        rfl

theorem cell23_836981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_836981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836981 prefixEnd_836981 := by exact prefixLift 836981
  have htrace : WordTrace (prefixWord ++ tailWord_836981) baseStart_836981 baseEnd_836981 := by
    simpa [prefixWord, tailWord_836981, baseEnd_836981] using wordTrace_append hprefix tailTrace_836981
  have hstable : (prefixWord ++ tailWord_836981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836981).length < 2 ^ (prefixWord ++ tailWord_836981).sum := by decide
  have hdescent : baseEnd_836981 < baseStart_836981 := by decide
  rcases family_descends (prefixWord ++ tailWord_836981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_836983 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_836983 : Nat := 118140960795 + 836983 * 2 ^ 59
def prefixEnd_836983 : Nat := 4983230072969 + 3 ^ 40 * 836983 * 2
def baseEnd_836983 : Nat := 429774578642204033863291

theorem tailTrace_836983 : CollatzResearch.WordTrace tailWord_836983 prefixEnd_836983 429774578642204033863291 := by
  unfold tailWord_836983
  simp only [CollatzResearch.WordTrace]
  refine ⟨30527277926761011161051603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20351518617840674107367735 30527277926761011161051603)
  ·
    refine ⟨45790916890141516741577405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30527277926761011161051603 45790916890141516741577405)
    ·
      refine ⟨17171593833803068778091527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45790916890141516741577405 17171593833803068778091527)
      ·
        refine ⟨25757390750704603167137291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17171593833803068778091527 25757390750704603167137291)
        ·
          refine ⟨38636086126056904750705937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25757390750704603167137291 38636086126056904750705937)
          ·
            refine ⟨28977064594542678563029453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38636086126056904750705937 28977064594542678563029453)
            ·
              refine ⟨10866399222953504461136045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28977064594542678563029453 10866399222953504461136045)
              ·
                refine ⟨4074899708607564172926017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10866399222953504461136045 4074899708607564172926017)
                ·
                  refine ⟨3056174781455673129694513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4074899708607564172926017 3056174781455673129694513)
                  ·
                    refine ⟨2292131086091754847270885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3056174781455673129694513 2292131086091754847270885)
                    ·
                      refine ⟨429774578642204033863291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2292131086091754847270885 429774578642204033863291)
                      ·
                        rfl

theorem cell23_836983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_836983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_836983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_836983 prefixEnd_836983 := by exact prefixLift 836983
  have htrace : WordTrace (prefixWord ++ tailWord_836983) baseStart_836983 baseEnd_836983 := by
    simpa [prefixWord, tailWord_836983, baseEnd_836983] using wordTrace_append hprefix tailTrace_836983
  have hstable : (prefixWord ++ tailWord_836983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_836983).length < 2 ^ (prefixWord ++ tailWord_836983).sum := by decide
  have hdescent : baseEnd_836983 < baseStart_836983 := by decide
  rcases family_descends (prefixWord ++ tailWord_836983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837027 : List Nat := [1, 1, 1, 4, 1, 3, 5, 2, 5]
def baseStart_837027 : Nat := 118140960795 + 837027 * 2 ^ 59
def prefixEnd_837027 : Nat := 4983230072969 + 3 ^ 40 * 837027 * 2
def baseEnd_837027 : Nat := 47755241310111317968121

theorem tailTrace_837027 : CollatzResearch.WordTrace tailWord_837027 prefixEnd_837027 47755241310111317968121 := by
  unfold tailWord_837027
  simp only [CollatzResearch.WordTrace]
  refine ⟨30528882738601606675653335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20352588492401071117102223 30528882738601606675653335)
  ·
    refine ⟨45793324107902410013480003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30528882738601606675653335 45793324107902410013480003)
    ·
      refine ⟨68689986161853615020220005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45793324107902410013480003 68689986161853615020220005)
      ·
        refine ⟨12879372405347552816291251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68689986161853615020220005 12879372405347552816291251)
        ·
          refine ⟨19319058608021329224436877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12879372405347552816291251 19319058608021329224436877)
          ·
            refine ⟨7244646978007998459163829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19319058608021329224436877 7244646978007998459163829)
            ·
              refine ⟨679185654188249855546609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7244646978007998459163829 679185654188249855546609)
              ·
                refine ⟨509389240641187391659957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679185654188249855546609 509389240641187391659957)
                ·
                  refine ⟨47755241310111317968121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 509389240641187391659957 47755241310111317968121)
                  ·
                    rfl

theorem cell23_837027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2, 5].length) (baseStart_837027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837027 prefixEnd_837027 := by exact prefixLift 837027
  have htrace : WordTrace (prefixWord ++ tailWord_837027) baseStart_837027 baseEnd_837027 := by
    simpa [prefixWord, tailWord_837027, baseEnd_837027] using wordTrace_append hprefix tailTrace_837027
  have hstable : (prefixWord ++ tailWord_837027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837027).length < 2 ^ (prefixWord ++ tailWord_837027).sum := by decide
  have hdescent : baseEnd_837027 < baseStart_837027 := by decide
  rcases family_descends (prefixWord ++ tailWord_837027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837043 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 4]
def baseStart_837043 : Nat := 118140960795 + 837043 * 2 ^ 59
def prefixEnd_837043 : Nat := 4983230072969 + 3 ^ 40 * 837043 * 2
def baseEnd_837043 : Nat := 429805387481473799113015

theorem tailTrace_837043 : CollatzResearch.WordTrace tailWord_837043 prefixEnd_837043 429805387481473799113015 := by
  unfold tailWord_837043
  simp only [CollatzResearch.WordTrace]
  refine ⟨30529466306543641408235783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20352977537695760938823855 30529466306543641408235783)
  ·
    refine ⟨45794199459815462112353675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30529466306543641408235783 45794199459815462112353675)
    ·
      refine ⟨68691299189723193168530513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45794199459815462112353675 68691299189723193168530513)
      ·
        refine ⟨51518474392292394876397885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68691299189723193168530513 51518474392292394876397885)
        ·
          refine ⟨19319427897109648078649207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51518474392292394876397885 19319427897109648078649207)
          ·
            refine ⟨28979141845664472117973811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19319427897109648078649207 28979141845664472117973811)
            ·
              refine ⟨43468712768496708176960717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28979141845664472117973811 43468712768496708176960717)
              ·
                refine ⟨16300767288186265566360269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43468712768496708176960717 16300767288186265566360269)
                ·
                  refine ⟨6112787733069849587385101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16300767288186265566360269 6112787733069849587385101)
                  ·
                    refine ⟨2292295399901193595269413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6112787733069849587385101 2292295399901193595269413)
                    ·
                      refine ⟨429805387481473799113015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2292295399901193595269413 429805387481473799113015)
                      ·
                        rfl

theorem cell23_837043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_837043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837043 prefixEnd_837043 := by exact prefixLift 837043
  have htrace : WordTrace (prefixWord ++ tailWord_837043) baseStart_837043 baseEnd_837043 := by
    simpa [prefixWord, tailWord_837043, baseEnd_837043] using wordTrace_append hprefix tailTrace_837043
  have hstable : (prefixWord ++ tailWord_837043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837043).length < 2 ^ (prefixWord ++ tailWord_837043).sum := by decide
  have hdescent : baseEnd_837043 < baseStart_837043 := by decide
  rcases family_descends (prefixWord ++ tailWord_837043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837077 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 2, 4, 2]
def baseStart_837077 : Nat := 118140960795 + 837077 * 2 ^ 59
def prefixEnd_837077 : Nat := 4983230072969 + 3 ^ 40 * 837077 * 2
def baseEnd_837077 : Nat := 429822845823726666087859

theorem tailTrace_837077 : CollatzResearch.WordTrace tailWord_837077 prefixEnd_837077 429822845823726666087859 := by
  unfold tailWord_837077
  simp only [CollatzResearch.WordTrace]
  refine ⟨30530706388420465214973485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20353804258946976809982323 30530706388420465214973485)
  ·
    refine ⟨11449014895657674455615057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30530706388420465214973485 11449014895657674455615057)
    ·
      refine ⟨8586761171743255841711293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11449014895657674455615057 8586761171743255841711293)
      ·
        refine ⟨3220035439403720940641735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8586761171743255841711293 3220035439403720940641735)
        ·
          refine ⟨4830053159105581410962603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3220035439403720940641735 4830053159105581410962603)
          ·
            refine ⟨7245079738658372116443905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830053159105581410962603 7245079738658372116443905)
            ·
              refine ⟨5433809803993779087332929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7245079738658372116443905 5433809803993779087332929)
              ·
                refine ⟨4075357352995334315499697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5433809803993779087332929 4075357352995334315499697)
                ·
                  refine ⟨3056518014746500736624773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4075357352995334315499697 3056518014746500736624773)
                  ·
                    refine ⟨573097127764968888117145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3056518014746500736624773 573097127764968888117145)
                    ·
                      refine ⟨429822845823726666087859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573097127764968888117145 429822845823726666087859)
                      ·
                        rfl

theorem cell23_837077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_837077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837077 prefixEnd_837077 := by exact prefixLift 837077
  have htrace : WordTrace (prefixWord ++ tailWord_837077) baseStart_837077 baseEnd_837077 := by
    simpa [prefixWord, tailWord_837077, baseEnd_837077] using wordTrace_append hprefix tailTrace_837077
  have hstable : (prefixWord ++ tailWord_837077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837077).length < 2 ^ (prefixWord ++ tailWord_837077).sum := by decide
  have hdescent : baseEnd_837077 < baseStart_837077 := by decide
  rcases family_descends (prefixWord ++ tailWord_837077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837121 : List Nat := [1, 2, 4, 1, 4, 1, 2, 3, 1, 4]
def baseStart_837121 : Nat := 118140960795 + 837121 * 2 ^ 59
def prefixEnd_837121 : Nat := 4983230072969 + 3 ^ 40 * 837121 * 2
def baseEnd_837121 : Nat := 143281812990841497979219

theorem tailTrace_837121 : CollatzResearch.WordTrace tailWord_837121 prefixEnd_837121 143281812990841497979219 := by
  unfold tailWord_837121
  simp only [CollatzResearch.WordTrace]
  refine ⟨30532311200261060729575217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20354874133507373819716811 30532311200261060729575217)
  ·
    refine ⟨22899233400195795547181413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30532311200261060729575217 22899233400195795547181413)
    ·
      refine ⟨4293606262536711665096515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22899233400195795547181413 4293606262536711665096515)
      ·
        refine ⟨6440409393805067497644773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4293606262536711665096515 6440409393805067497644773)
        ·
          refine ⟨1207576761338450155808395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6440409393805067497644773 1207576761338450155808395)
          ·
            refine ⟨1811365142007675233712593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207576761338450155808395 1811365142007675233712593)
            ·
              refine ⟨1358523856505756425284445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1811365142007675233712593 1358523856505756425284445)
              ·
                refine ⟨509446446189658659481667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1358523856505756425284445 509446446189658659481667)
                ·
                  refine ⟨764169669284487989222501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509446446189658659481667 764169669284487989222501)
                  ·
                    refine ⟨143281812990841497979219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 764169669284487989222501 143281812990841497979219)
                    ·
                      rfl

theorem cell23_837121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_837121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837121 prefixEnd_837121 := by exact prefixLift 837121
  have htrace : WordTrace (prefixWord ++ tailWord_837121) baseStart_837121 baseEnd_837121 := by
    simpa [prefixWord, tailWord_837121, baseEnd_837121] using wordTrace_append hprefix tailTrace_837121
  have hstable : (prefixWord ++ tailWord_837121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837121).length < 2 ^ (prefixWord ++ tailWord_837121).sum := by decide
  have hdescent : baseEnd_837121 < baseStart_837121 := by decide
  rcases family_descends (prefixWord ++ tailWord_837121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837134 : List Nat := [4, 1, 1, 2, 4, 2, 1, 2, 6]
def baseStart_837134 : Nat := 118140960795 + 837134 * 2 ^ 59
def prefixEnd_837134 : Nat := 4983230072969 + 3 ^ 40 * 837134 * 2
def baseEnd_837134 : Nat := 47761346024559215897233

theorem tailTrace_837134 : CollatzResearch.WordTrace tailWord_837134 prefixEnd_837134 47761346024559215897233 := by
  unfold tailWord_837134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3816598168651745493724807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20355190232809309299865637 3816598168651745493724807)
  ·
    refine ⟨5724897252977618240587211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3816598168651745493724807 5724897252977618240587211)
    ·
      refine ⟨8587345879466427360880817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5724897252977618240587211 8587345879466427360880817)
      ·
        refine ⟨6440509409599820520660613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8587345879466427360880817 6440509409599820520660613)
        ·
          refine ⟨1207595514299966347623865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6440509409599820520660613 1207595514299966347623865)
          ·
            refine ⟨905696635724974760717899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1207595514299966347623865 905696635724974760717899)
            ·
              refine ⟨1358544953587462141076849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905696635724974760717899 1358544953587462141076849)
              ·
                refine ⟨1018908715190596605807637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358544953587462141076849 1018908715190596605807637)
                ·
                  refine ⟨47761346024559215897233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1018908715190596605807637 47761346024559215897233)
                  ·
                    rfl

theorem cell23_837134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_837134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837134 prefixEnd_837134 := by exact prefixLift 837134
  have htrace : WordTrace (prefixWord ++ tailWord_837134) baseStart_837134 baseEnd_837134 := by
    simpa [prefixWord, tailWord_837134, baseEnd_837134] using wordTrace_append hprefix tailTrace_837134
  have hstable : (prefixWord ++ tailWord_837134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837134).length < 2 ^ (prefixWord ++ tailWord_837134).sum := by decide
  have hdescent : baseEnd_837134 < baseStart_837134 := by decide
  rcases family_descends (prefixWord ++ tailWord_837134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837137 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 4, 3, 2]
def baseStart_837137 : Nat := 118140960795 + 837137 * 2 ^ 59
def prefixEnd_837137 : Nat := 4983230072969 + 3 ^ 40 * 837137 * 2
def baseEnd_837137 : Nat := 429853654662996431337583

theorem tailTrace_837137 : CollatzResearch.WordTrace tailWord_837137 prefixEnd_837137 429853654662996431337583 := by
  unfold tailWord_837137
  simp only [CollatzResearch.WordTrace]
  refine ⟨30532894768203095462157665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20355263178802063641438443 30532894768203095462157665)
  ·
    refine ⟨22899671076152321596618249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30532894768203095462157665 22899671076152321596618249)
    ·
      refine ⟨17174753307114241197463687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22899671076152321596618249 17174753307114241197463687)
      ·
        refine ⟨25762129960671361796195531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17174753307114241197463687 25762129960671361796195531)
        ·
          refine ⟨38643194941007042694293297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25762129960671361796195531 38643194941007042694293297)
          ·
            refine ⟨28982396205755282020719973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38643194941007042694293297 28982396205755282020719973)
            ·
              refine ⟨5434199288579115378884995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28982396205755282020719973 5434199288579115378884995)
              ·
                refine ⟨8151298932868673068327493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5434199288579115378884995 8151298932868673068327493)
                ·
                  refine ⟨1528368549912876200311405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8151298932868673068327493 1528368549912876200311405)
                  ·
                    refine ⟨573138206217328575116777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1528368549912876200311405 573138206217328575116777)
                    ·
                      refine ⟨429853654662996431337583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573138206217328575116777 429853654662996431337583)
                      ·
                        rfl

theorem cell23_837137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 3, 2].length) (baseStart_837137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837137 prefixEnd_837137 := by exact prefixLift 837137
  have htrace : WordTrace (prefixWord ++ tailWord_837137) baseStart_837137 baseEnd_837137 := by
    simpa [prefixWord, tailWord_837137, baseEnd_837137] using wordTrace_append hprefix tailTrace_837137
  have hstable : (prefixWord ++ tailWord_837137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837137).length < 2 ^ (prefixWord ++ tailWord_837137).sum := by decide
  have hdescent : baseEnd_837137 < baseStart_837137 := by decide
  rcases family_descends (prefixWord ++ tailWord_837137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837170 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_837170 : Nat := 118140960795 + 837170 * 2 ^ 59
def prefixEnd_837170 : Nat := 4983230072969 + 3 ^ 40 * 837170 * 2
def baseEnd_837170 : Nat := 429870599524594802224931

theorem tailTrace_837170 : CollatzResearch.WordTrace tailWord_837170 prefixEnd_837170 429870599524594802224931 := by
  unfold tailWord_837170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7633524594270885524527241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20356065584722361398739309 7633524594270885524527241)
  ·
    refine ⟨5725143445703164143395431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7633524594270885524527241 5725143445703164143395431)
    ·
      refine ⟨8587715168554746215093147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5725143445703164143395431 8587715168554746215093147)
      ·
        refine ⟨12881572752832119322639721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8587715168554746215093147 12881572752832119322639721)
        ·
          refine ⟨9661179564624089491979791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12881572752832119322639721 9661179564624089491979791)
          ·
            refine ⟨14491769346936134237969687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9661179564624089491979791 14491769346936134237969687)
            ·
              refine ⟨21737654020404201356954531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14491769346936134237969687 21737654020404201356954531)
              ·
                refine ⟨32606481030606302035431797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21737654020404201356954531 32606481030606302035431797)
                ·
                  refine ⟨3056857596619340815821731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32606481030606302035431797 3056857596619340815821731)
                  ·
                    refine ⟨4585286394929011223732597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3056857596619340815821731 4585286394929011223732597)
                    ·
                      refine ⟨429870599524594802224931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4585286394929011223732597 429870599524594802224931)
                      ·
                        rfl

theorem cell23_837170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_837170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837170 prefixEnd_837170 := by exact prefixLift 837170
  have htrace : WordTrace (prefixWord ++ tailWord_837170) baseStart_837170 baseEnd_837170 := by
    simpa [prefixWord, tailWord_837170, baseEnd_837170] using wordTrace_append hprefix tailTrace_837170
  have hstable : (prefixWord ++ tailWord_837170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837170).length < 2 ^ (prefixWord ++ tailWord_837170).sum := by decide
  have hdescent : baseEnd_837170 < baseStart_837170 := by decide
  rcases family_descends (prefixWord ++ tailWord_837170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837177 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 4, 4]
def baseStart_837177 : Nat := 118140960795 + 837177 * 2 ^ 59
def prefixEnd_837177 : Nat := 4983230072969 + 3 ^ 40 * 837177 * 2
def baseEnd_837177 : Nat := 143291397963058758279133

theorem tailTrace_837177 : CollatzResearch.WordTrace tailWord_837177 prefixEnd_837177 143291397963058758279133 := by
  unfold tailWord_837177
  simp only [CollatzResearch.WordTrace]
  refine ⟨30534353688058182293613785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20356235792038788195742523 30534353688058182293613785)
  ·
    refine ⟨22900765266043636720210339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30534353688058182293613785 22900765266043636720210339)
    ·
      refine ⟨34351147899065455080315509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22900765266043636720210339 34351147899065455080315509)
      ·
        refine ⟨3220420115537386413779579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34351147899065455080315509 3220420115537386413779579)
        ·
          refine ⟨4830630173306079620669369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3220420115537386413779579 4830630173306079620669369)
          ·
            refine ⟨3622972629979559715502027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4830630173306079620669369 3622972629979559715502027)
            ·
              refine ⟨5434458944969339573253041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3622972629979559715502027 5434458944969339573253041)
              ·
                refine ⟨4075844208727004679939781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5434458944969339573253041 4075844208727004679939781)
                ·
                  refine ⟨764220789136313377488709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4075844208727004679939781 764220789136313377488709)
                  ·
                    refine ⟨143291397963058758279133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 764220789136313377488709 143291397963058758279133)
                    ·
                      rfl

theorem cell23_837177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4, 4].length) (baseStart_837177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837177 prefixEnd_837177 := by exact prefixLift 837177
  have htrace : WordTrace (prefixWord ++ tailWord_837177) baseStart_837177 baseEnd_837177 := by
    simpa [prefixWord, tailWord_837177, baseEnd_837177] using wordTrace_append hprefix tailTrace_837177
  have hstable : (prefixWord ++ tailWord_837177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837177).length < 2 ^ (prefixWord ++ tailWord_837177).sum := by decide
  have hdescent : baseEnd_837177 < baseStart_837177 := by decide
  rcases family_descends (prefixWord ++ tailWord_837177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837217 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 1, 3, 3]
def baseStart_837217 : Nat := 118140960795 + 837217 * 2 ^ 59
def prefixEnd_837217 : Nat := 4983230072969 + 3 ^ 40 * 837217 * 2
def baseEnd_837217 : Nat := 429894733115356118337215

theorem tailTrace_837217 : CollatzResearch.WordTrace tailWord_837217 prefixEnd_837217 429894733115356118337215 := by
  unfold tailWord_837217
  simp only [CollatzResearch.WordTrace]
  refine ⟨30535812607913269125069905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20357208405275512750046603 30535812607913269125069905)
  ·
    refine ⟨22901859455934951843802429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30535812607913269125069905 22901859455934951843802429)
    ·
      refine ⟨8588197295975606941425911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22901859455934951843802429 8588197295975606941425911)
      ·
        refine ⟨12882295943963410412138867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8588197295975606941425911 12882295943963410412138867)
        ·
          refine ⟨19323443915945115618208301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12882295943963410412138867 19323443915945115618208301)
          ·
            refine ⟨7246291468479418356828113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19323443915945115618208301 7246291468479418356828113)
            ·
              refine ⟨5434718601359563767621085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7246291468479418356828113 5434718601359563767621085)
              ·
                refine ⟨2038019475509836412857907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5434718601359563767621085 2038019475509836412857907)
                ·
                  refine ⟨3057029213264754619286861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038019475509836412857907 3057029213264754619286861)
                  ·
                    refine ⟨1146385954974282982232573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3057029213264754619286861 1146385954974282982232573)
                    ·
                      refine ⟨429894733115356118337215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1146385954974282982232573 429894733115356118337215)
                      ·
                        rfl

theorem cell23_837217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_837217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837217 prefixEnd_837217 := by exact prefixLift 837217
  have htrace : WordTrace (prefixWord ++ tailWord_837217) baseStart_837217 baseEnd_837217 := by
    simpa [prefixWord, tailWord_837217, baseEnd_837217] using wordTrace_append hprefix tailTrace_837217
  have hstable : (prefixWord ++ tailWord_837217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837217).length < 2 ^ (prefixWord ++ tailWord_837217).sum := by decide
  have hdescent : baseEnd_837217 < baseStart_837217 := by decide
  rcases family_descends (prefixWord ++ tailWord_837217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837221 : List Nat := [1, 3, 1, 3, 3, 3, 1, 2, 1, 2, 3]
def baseStart_837221 : Nat := 118140960795 + 837221 * 2 ^ 59
def prefixEnd_837221 : Nat := 4983230072969 + 3 ^ 40 * 837221 * 2
def baseEnd_837221 : Nat := 429896787037974102687197

theorem tailTrace_837221 : CollatzResearch.WordTrace tailWord_837221 prefixEnd_837221 429896787037974102687197 := by
  unfold tailWord_837221
  simp only [CollatzResearch.WordTrace]
  refine ⟨30535958499898777808215517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20357305666599185205477011 30535958499898777808215517)
  ·
    refine ⟨11450984437462041678080819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30535958499898777808215517 11450984437462041678080819)
    ·
      refine ⟨17176476656193062517121229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11450984437462041678080819 17176476656193062517121229)
      ·
        refine ⟨6441178746072398443920461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17176476656193062517121229 6441178746072398443920461)
        ·
          refine ⟨2415442029777149416470173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6441178746072398443920461 2415442029777149416470173)
          ·
            refine ⟨905790761166431031176315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2415442029777149416470173 905790761166431031176315)
            ·
              refine ⟨1358686141749646546764473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905790761166431031176315 1358686141749646546764473)
              ·
                refine ⟨1019014606312234910073355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358686141749646546764473 1019014606312234910073355)
                ·
                  refine ⟨1528521909468352365110033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019014606312234910073355 1528521909468352365110033)
                  ·
                    refine ⟨1146391432101264273832525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1528521909468352365110033 1146391432101264273832525)
                    ·
                      refine ⟨429896787037974102687197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1146391432101264273832525 429896787037974102687197)
                      ·
                        rfl

theorem cell23_837221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_837221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837221 prefixEnd_837221 := by exact prefixLift 837221
  have htrace : WordTrace (prefixWord ++ tailWord_837221) baseStart_837221 baseEnd_837221 := by
    simpa [prefixWord, tailWord_837221, baseEnd_837221] using wordTrace_append hprefix tailTrace_837221
  have hstable : (prefixWord ++ tailWord_837221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837221).length < 2 ^ (prefixWord ++ tailWord_837221).sum := by decide
  have hdescent : baseEnd_837221 < baseStart_837221 := by decide
  rcases family_descends (prefixWord ++ tailWord_837221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837234 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_837234 : Nat := 118140960795 + 837234 * 2 ^ 59
def prefixEnd_837234 : Nat := 4983230072969 + 3 ^ 40 * 837234 * 2
def baseEnd_837234 : Nat := 429903462286482551824637

theorem tailTrace_837234 : CollatzResearch.WordTrace tailWord_837234 prefixEnd_837234 429903462286482551824637 := by
  unfold tailWord_837234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7634108162212920257109689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20357621765901120685625837 7634108162212920257109689)
  ·
    refine ⟨5725581121659690192832267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7634108162212920257109689 5725581121659690192832267)
    ·
      refine ⟨8588371682489535289248401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5725581121659690192832267 8588371682489535289248401)
      ·
        refine ⟨6441278761867151466936301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8588371682489535289248401 6441278761867151466936301)
        ·
          refine ⟨2415479535700181800101113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6441278761867151466936301 2415479535700181800101113)
          ·
            refine ⟨1811609651775136350075835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2415479535700181800101113 1811609651775136350075835)
            ·
              refine ⟨2717414477662704525113753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811609651775136350075835 2717414477662704525113753)
              ·
                refine ⟨2038060858247028393835315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2717414477662704525113753 2038060858247028393835315)
                ·
                  refine ⟨3057091287370542590752973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038060858247028393835315 3057091287370542590752973)
                  ·
                    refine ⟨1146409232763953471532365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3057091287370542590752973 1146409232763953471532365)
                    ·
                      refine ⟨429903462286482551824637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1146409232763953471532365 429903462286482551824637)
                      ·
                        rfl

theorem cell23_837234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_837234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837234 prefixEnd_837234 := by exact prefixLift 837234
  have htrace : WordTrace (prefixWord ++ tailWord_837234) baseStart_837234 baseEnd_837234 := by
    simpa [prefixWord, tailWord_837234, baseEnd_837234] using wordTrace_append hprefix tailTrace_837234
  have hstable : (prefixWord ++ tailWord_837234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837234).length < 2 ^ (prefixWord ++ tailWord_837234).sum := by decide
  have hdescent : baseEnd_837234 < baseStart_837234 := by decide
  rcases family_descends (prefixWord ++ tailWord_837234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837238 : List Nat := [5, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_837238 : Nat := 118140960795 + 837238 * 2 ^ 59
def prefixEnd_837238 : Nat := 4983230072969 + 3 ^ 40 * 837238 * 2
def baseEnd_837238 : Nat := 429905516209100536174619

theorem tailTrace_837238 : CollatzResearch.WordTrace tailWord_837238 prefixEnd_837238 429905516209100536174619 := by
  unfold tailWord_837238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908536158802324356974023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20357719027224793141056245 1908536158802324356974023)
  ·
    refine ⟨2862804238203486535461035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1908536158802324356974023 2862804238203486535461035)
    ·
      refine ⟨4294206357305229803191553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2862804238203486535461035 4294206357305229803191553)
      ·
        refine ⟨3220654767978922352393665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4294206357305229803191553 3220654767978922352393665)
        ·
          refine ⟨2415491075984191764295249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3220654767978922352393665 2415491075984191764295249)
          ·
            refine ⟨1811618306988143823221437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2415491075984191764295249 1811618306988143823221437)
            ·
              refine ⟨679356865120553933708039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1811618306988143823221437 679356865120553933708039)
              ·
                refine ⟨1019035297680830900562059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679356865120553933708039 1019035297680830900562059)
                ·
                  refine ⟨1528552946521246350843089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019035297680830900562059 1528552946521246350843089)
                  ·
                    refine ⟨1146414709890934763132317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1528552946521246350843089 1146414709890934763132317)
                    ·
                      refine ⟨429905516209100536174619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1146414709890934763132317 429905516209100536174619)
                      ·
                        rfl

theorem cell23_837238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_837238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837238 prefixEnd_837238 := by exact prefixLift 837238
  have htrace : WordTrace (prefixWord ++ tailWord_837238) baseStart_837238 baseEnd_837238 := by
    simpa [prefixWord, tailWord_837238, baseEnd_837238] using wordTrace_append hprefix tailTrace_837238
  have hstable : (prefixWord ++ tailWord_837238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837238).length < 2 ^ (prefixWord ++ tailWord_837238).sum := by decide
  have hdescent : baseEnd_837238 < baseStart_837238 := by decide
  rcases family_descends (prefixWord ++ tailWord_837238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837240 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_837240 : Nat := 118140960795 + 837240 * 2 ^ 59
def prefixEnd_837240 : Nat := 4983230072969 + 3 ^ 40 * 837240 * 2
def baseEnd_837240 : Nat := 429906543170409528349609

theorem tailTrace_837240 : CollatzResearch.WordTrace tailWord_837240 prefixEnd_837240 429906543170409528349609 := by
  unfold tailWord_837240
  simp only [CollatzResearch.WordTrace]
  refine ⟨15268325743414972026578587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20357767657886629368771449 15268325743414972026578587)
  ·
    refine ⟨22902488615122458039867881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15268325743414972026578587 22902488615122458039867881)
    ·
      refine ⟨17176866461341843529900911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22902488615122458039867881 17176866461341843529900911)
      ·
        refine ⟨25765299692012765294851367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17176866461341843529900911 25765299692012765294851367)
        ·
          refine ⟨38647949538019147942277051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25765299692012765294851367 38647949538019147942277051)
          ·
            refine ⟨57971924307028721913415577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38647949538019147942277051 57971924307028721913415577)
            ·
              refine ⟨43478943230271541435061683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57971924307028721913415577 43478943230271541435061683)
              ·
                refine ⟨65218414845407312152592525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43478943230271541435061683 65218414845407312152592525)
                ·
                  refine ⟨24456905567027742057222197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65218414845407312152592525 24456905567027742057222197)
                  ·
                    refine ⟨2292834896908850817864581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24456905567027742057222197 2292834896908850817864581)
                    ·
                      refine ⟨429906543170409528349609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2292834896908850817864581 429906543170409528349609)
                      ·
                        rfl

theorem cell23_837240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_837240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837240 prefixEnd_837240 := by exact prefixLift 837240
  have htrace : WordTrace (prefixWord ++ tailWord_837240) baseStart_837240 baseEnd_837240 := by
    simpa [prefixWord, tailWord_837240, baseEnd_837240] using wordTrace_append hprefix tailTrace_837240
  have hstable : (prefixWord ++ tailWord_837240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837240).length < 2 ^ (prefixWord ++ tailWord_837240).sum := by decide
  have hdescent : baseEnd_837240 < baseStart_837240 := by decide
  rcases family_descends (prefixWord ++ tailWord_837240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837252 : List Nat := [2, 3, 2, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_837252 : Nat := 118140960795 + 837252 * 2 ^ 59
def prefixEnd_837252 : Nat := 4983230072969 + 3 ^ 40 * 837252 * 2
def baseEnd_837252 : Nat := 429912704938263481399555

theorem tailTrace_837252 : CollatzResearch.WordTrace tailWord_837252 prefixEnd_837252 429912704938263481399555 := by
  unfold tailWord_837252
  simp only [CollatzResearch.WordTrace]
  refine ⟨15268544581393235051297005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20358059441857646735062673 15268544581393235051297005)
  ·
    refine ⟨5725704218022463144236377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15268544581393235051297005 5725704218022463144236377)
    ·
      refine ⟨4294278163516847358177283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5725704218022463144236377 4294278163516847358177283)
      ·
        refine ⟨6441417245275271037265925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294278163516847358177283 6441417245275271037265925)
        ·
          refine ⟨1207765733489113319487361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6441417245275271037265925 1207765733489113319487361)
          ·
            refine ⟨905824300116834989615521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1207765733489113319487361 905824300116834989615521)
            ·
              refine ⟨679368225087626242211641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 905824300116834989615521 679368225087626242211641)
              ·
                refine ⟨509526168815719681658731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679368225087626242211641 509526168815719681658731)
                ·
                  refine ⟨764289253223579522488097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509526168815719681658731 764289253223579522488097)
                  ·
                    refine ⟨573216939917684641866073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 764289253223579522488097 573216939917684641866073)
                    ·
                      refine ⟨429912704938263481399555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573216939917684641866073 429912704938263481399555)
                      ·
                        rfl

theorem cell23_837252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_837252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837252 prefixEnd_837252 := by exact prefixLift 837252
  have htrace : WordTrace (prefixWord ++ tailWord_837252) baseStart_837252 baseEnd_837252 := by
    simpa [prefixWord, tailWord_837252, baseEnd_837252] using wordTrace_append hprefix tailTrace_837252
  have hstable : (prefixWord ++ tailWord_837252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837252).length < 2 ^ (prefixWord ++ tailWord_837252).sum := by decide
  have hdescent : baseEnd_837252 < baseStart_837252 := by decide
  rcases family_descends (prefixWord ++ tailWord_837252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837277 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_837277 : Nat := 118140960795 + 837277 * 2 ^ 59
def prefixEnd_837277 : Nat := 4983230072969 + 3 ^ 40 * 837277 * 2
def baseEnd_837277 : Nat := 429925541954625883586939

theorem tailTrace_837277 : CollatzResearch.WordTrace tailWord_837277 prefixEnd_837277 429925541954625883586939 := by
  unfold tailWord_837277
  simp only [CollatzResearch.WordTrace]
  refine ⟨30538000987695899372254085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20358667325130599581502723 30538000987695899372254085)
  ·
    refine ⟨5725875185192981132297641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30538000987695899372254085 5725875185192981132297641)
    ·
      refine ⟨4294406388894735849223231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5725875185192981132297641 4294406388894735849223231)
      ·
        refine ⟨6441609583342103773834847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294406388894735849223231 6441609583342103773834847)
        ·
          refine ⟨9662414375013155660752271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441609583342103773834847 9662414375013155660752271)
          ·
            refine ⟨14493621562519733491128407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9662414375013155660752271 14493621562519733491128407)
            ·
              refine ⟨21740432343779600236692611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14493621562519733491128407 21740432343779600236692611)
              ·
                refine ⟨32610648515669400355038917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21740432343779600236692611 32610648515669400355038917)
                ·
                  refine ⟨6114496596688012566569797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32610648515669400355038917 6114496596688012566569797)
                  ·
                    refine ⟨1146468111879002356231837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6114496596688012566569797 1146468111879002356231837)
                    ·
                      refine ⟨429925541954625883586939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1146468111879002356231837 429925541954625883586939)
                      ·
                        rfl

theorem cell23_837277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_837277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837277 prefixEnd_837277 := by exact prefixLift 837277
  have htrace : WordTrace (prefixWord ++ tailWord_837277) baseStart_837277 baseEnd_837277 := by
    simpa [prefixWord, tailWord_837277, baseEnd_837277] using wordTrace_append hprefix tailTrace_837277
  have hstable : (prefixWord ++ tailWord_837277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837277).length < 2 ^ (prefixWord ++ tailWord_837277).sum := by decide
  have hdescent : baseEnd_837277 < baseStart_837277 := by decide
  rcases family_descends (prefixWord ++ tailWord_837277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837308 : List Nat := [2, 2, 2, 3, 1, 2, 3, 2, 2, 2, 2]
def baseStart_837308 : Nat := 118140960795 + 837308 * 2 ^ 59
def prefixEnd_837308 : Nat := 4983230072969 + 3 ^ 40 * 837308 * 2
def baseEnd_837308 : Nat := 429941459854915262299297

theorem tailTrace_837308 : CollatzResearch.WordTrace tailWord_837308 prefixEnd_837308 429941459854915262299297 := by
  unfold tailWord_837308
  simp only [CollatzResearch.WordTrace]
  refine ⟨15269565825291795833316289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20359421100389061111088385 15269565825291795833316289)
  ·
    refine ⟨11452174368968846874987217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15269565825291795833316289 11452174368968846874987217)
    ·
      refine ⟨8589130776726635156240413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11452174368968846874987217 8589130776726635156240413)
      ·
        refine ⟨3220924041272488183590155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8589130776726635156240413 3220924041272488183590155)
        ·
          refine ⟨4831386061908732275385233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3220924041272488183590155 4831386061908732275385233)
          ·
            refine ⟨3623539546431549206538925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4831386061908732275385233 3623539546431549206538925)
            ·
              refine ⟨1358827329911830952452097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3623539546431549206538925 1358827329911830952452097)
              ·
                refine ⟨1019120497433873214339073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358827329911830952452097 1019120497433873214339073)
                ·
                  refine ⟨764340373075404910754305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1019120497433873214339073 764340373075404910754305)
                  ·
                    refine ⟨573255279806553683065729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 764340373075404910754305 573255279806553683065729)
                    ·
                      refine ⟨429941459854915262299297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573255279806553683065729 429941459854915262299297)
                      ·
                        rfl

theorem cell23_837308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_837308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837308 prefixEnd_837308 := by exact prefixLift 837308
  have htrace : WordTrace (prefixWord ++ tailWord_837308) baseStart_837308 baseEnd_837308 := by
    simpa [prefixWord, tailWord_837308, baseEnd_837308] using wordTrace_append hprefix tailTrace_837308
  have hstable : (prefixWord ++ tailWord_837308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837308).length < 2 ^ (prefixWord ++ tailWord_837308).sum := by decide
  have hdescent : baseEnd_837308 < baseStart_837308 := by decide
  rcases family_descends (prefixWord ++ tailWord_837308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837325 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_837325 : Nat := 118140960795 + 837325 * 2 ^ 59
def prefixEnd_837325 : Nat := 4983230072969 + 3 ^ 40 * 837325 * 2
def baseEnd_837325 : Nat := 429950189026041695786719

theorem tailTrace_837325 : CollatzResearch.WordTrace tailWord_837325 prefixEnd_837325 429950189026041695786719 := by
  unfold tailWord_837325
  simp only [CollatzResearch.WordTrace]
  refine ⟨30539751691522003570001429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20359834461014669046667619 30539751691522003570001429)
  ·
    refine ⟨1431550860540093917343817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30539751691522003570001429 1431550860540093917343817)
    ·
      refine ⟨1073663145405070438007863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1431550860540093917343817 1073663145405070438007863)
      ·
        refine ⟨1610494718107605657011795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1073663145405070438007863 1610494718107605657011795)
        ·
          refine ⟨2415742077161408485517693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610494718107605657011795 2415742077161408485517693)
          ·
            refine ⟨905903278935528182069135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2415742077161408485517693 905903278935528182069135)
            ·
              refine ⟨1358854918403292273103703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905903278935528182069135 1358854918403292273103703)
              ·
                refine ⟨2038282377604938409655555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358854918403292273103703 2038282377604938409655555)
                ·
                  refine ⟨3057423566407407614483333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038282377604938409655555 3057423566407407614483333)
                  ·
                    refine ⟨573266918701388927715625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3057423566407407614483333 573266918701388927715625)
                    ·
                      refine ⟨429950189026041695786719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573266918701388927715625 429950189026041695786719)
                      ·
                        rfl

theorem cell23_837325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_837325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837325 prefixEnd_837325 := by exact prefixLift 837325
  have htrace : WordTrace (prefixWord ++ tailWord_837325) baseStart_837325 baseEnd_837325 := by
    simpa [prefixWord, tailWord_837325, baseEnd_837325] using wordTrace_append hprefix tailTrace_837325
  have hstable : (prefixWord ++ tailWord_837325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837325).length < 2 ^ (prefixWord ++ tailWord_837325).sum := by decide
  have hdescent : baseEnd_837325 < baseStart_837325 := by decide
  rcases family_descends (prefixWord ++ tailWord_837325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837377 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_837377 : Nat := 118140960795 + 837377 * 2 ^ 59
def prefixEnd_837377 : Nat := 4983230072969 + 3 ^ 40 * 837377 * 2
def baseEnd_837377 : Nat := 429976890020075492336479

theorem tailTrace_837377 : CollatzResearch.WordTrace tailWord_837377 prefixEnd_837377 429976890020075492336479 := by
  unfold tailWord_837377
  simp only [CollatzResearch.WordTrace]
  refine ⟨30541648287333616450894385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20361098858222410967262923 30541648287333616450894385)
  ·
    refine ⟨22906236215500212338170789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30541648287333616450894385 22906236215500212338170789)
    ·
      refine ⟨4294919290406289813407023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22906236215500212338170789 4294919290406289813407023)
      ·
        refine ⟨6442378935609434720110535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294919290406289813407023 6442378935609434720110535)
        ·
          refine ⟨9663568403414152080165803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6442378935609434720110535 9663568403414152080165803)
          ·
            refine ⟨14495352605121228120248705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9663568403414152080165803 14495352605121228120248705)
            ·
              refine ⟨10871514453840921090186529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14495352605121228120248705 10871514453840921090186529)
              ·
                refine ⟨8153635840380690817639897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10871514453840921090186529 8153635840380690817639897)
                ·
                  refine ⟨6115226880285518113229923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8153635840380690817639897 6115226880285518113229923)
                  ·
                    refine ⟨9172840320428277169844885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6115226880285518113229923 9172840320428277169844885)
                    ·
                      refine ⟨429976890020075492336479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 9172840320428277169844885 429976890020075492336479)
                      ·
                        rfl

theorem cell23_837377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_837377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837377 prefixEnd_837377 := by exact prefixLift 837377
  have htrace : WordTrace (prefixWord ++ tailWord_837377) baseStart_837377 baseEnd_837377 := by
    simpa [prefixWord, tailWord_837377, baseEnd_837377] using wordTrace_append hprefix tailTrace_837377
  have hstable : (prefixWord ++ tailWord_837377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837377).length < 2 ^ (prefixWord ++ tailWord_837377).sum := by decide
  have hdescent : baseEnd_837377 < baseStart_837377 := by decide
  rcases family_descends (prefixWord ++ tailWord_837377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837384 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_837384 : Nat := 118140960795 + 837384 * 2 ^ 59
def prefixEnd_837384 : Nat := 4983230072969 + 3 ^ 40 * 837384 * 2
def baseEnd_837384 : Nat := 429980484384656964948947

theorem tailTrace_837384 : CollatzResearch.WordTrace tailWord_837384 prefixEnd_837384 429980484384656964948947 := by
  unfold tailWord_837384
  simp only [CollatzResearch.WordTrace]
  refine ⟨15270951799154128323199603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20361269065538837764266137 15270951799154128323199603)
  ·
    refine ⟨22906427698731192484799405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15270951799154128323199603 22906427698731192484799405)
    ·
      refine ⟨8589910387024197181799777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22906427698731192484799405 8589910387024197181799777)
      ·
        refine ⟨6442432790268147886349833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8589910387024197181799777 6442432790268147886349833)
        ·
          refine ⟨4831824592701110914762375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6442432790268147886349833 4831824592701110914762375)
          ·
            refine ⟨7247736889051666372143563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4831824592701110914762375 7247736889051666372143563)
            ·
              refine ⟨10871605333577499558215345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7247736889051666372143563 10871605333577499558215345)
              ·
                refine ⟨8153704000183124668661509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10871605333577499558215345 8153704000183124668661509)
                ·
                  refine ⟨1528819500034335875374033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8153704000183124668661509 1528819500034335875374033)
                  ·
                    refine ⟨1146614625025751906530525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1528819500034335875374033 1146614625025751906530525)
                    ·
                      refine ⟨429980484384656964948947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1146614625025751906530525 429980484384656964948947)
                      ·
                        rfl

theorem cell23_837384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_837384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837384 prefixEnd_837384 := by exact prefixLift 837384
  have htrace : WordTrace (prefixWord ++ tailWord_837384) baseStart_837384 baseEnd_837384 := by
    simpa [prefixWord, tailWord_837384, baseEnd_837384] using wordTrace_append hprefix tailTrace_837384
  have hstable : (prefixWord ++ tailWord_837384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837384).length < 2 ^ (prefixWord ++ tailWord_837384).sum := by decide
  have hdescent : baseEnd_837384 < baseStart_837384 := by decide
  rcases family_descends (prefixWord ++ tailWord_837384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837417 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 7, 5]
def baseStart_837417 : Nat := 118140960795 + 837417 * 2 ^ 59
def prefixEnd_837417 : Nat := 4983230072969 + 3 ^ 40 * 837417 * 2
def baseEnd_837417 : Nat := 143332476415418445278765

theorem tailTrace_837417 : CollatzResearch.WordTrace tailWord_837417 prefixEnd_837417 143332476415418445278765 := by
  unfold tailWord_837417
  simp only [CollatzResearch.WordTrace]
  refine ⟨30543107207188703282350505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20362071471459135521567003 30543107207188703282350505)
  ·
    refine ⟨22907330405391527461762879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30543107207188703282350505 22907330405391527461762879)
    ·
      refine ⟨34360995608087291192644319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22907330405391527461762879 34360995608087291192644319)
      ·
        refine ⟨51541493412130936788966479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34360995608087291192644319 51541493412130936788966479)
        ·
          refine ⟨77312240118196405183449719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51541493412130936788966479 77312240118196405183449719)
          ·
            refine ⟨115968360177294607775174579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77312240118196405183449719 115968360177294607775174579)
            ·
              refine ⟨173952540265941911662761869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115968360177294607775174579 173952540265941911662761869)
              ·
                refine ⟨65232202599728216873535701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173952540265941911662761869 65232202599728216873535701)
                ·
                  refine ⟨1528879748431130082973493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 65232202599728216873535701 1528879748431130082973493)
                  ·
                    refine ⟨143332476415418445278765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1528879748431130082973493 143332476415418445278765)
                    ·
                      rfl

theorem cell23_837417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 7, 5].length) (baseStart_837417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837417 prefixEnd_837417 := by exact prefixLift 837417
  have htrace : WordTrace (prefixWord ++ tailWord_837417) baseStart_837417 baseEnd_837417 := by
    simpa [prefixWord, tailWord_837417, baseEnd_837417] using wordTrace_append hprefix tailTrace_837417
  have hstable : (prefixWord ++ tailWord_837417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837417).length < 2 ^ (prefixWord ++ tailWord_837417).sum := by decide
  have hdescent : baseEnd_837417 < baseStart_837417 := by decide
  rcases family_descends (prefixWord ++ tailWord_837417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837424 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 5, 5, 2]
def baseStart_837424 : Nat := 118140960795 + 837424 * 2 ^ 59
def prefixEnd_837424 : Nat := 4983230072969 + 3 ^ 40 * 837424 * 2
def baseEnd_837424 : Nat := 430001023610836808448763

theorem tailTrace_837424 : CollatzResearch.WordTrace tailWord_837424 prefixEnd_837424 430001023610836808448763 := by
  unfold tailWord_837424
  simp only [CollatzResearch.WordTrace]
  refine ⟨15271681259081671738927663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20362241678775562318570217 15271681259081671738927663)
  ·
    refine ⟨22907521888622507608391495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15271681259081671738927663 22907521888622507608391495)
    ·
      refine ⟨34361282832933761412587243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22907521888622507608391495 34361282832933761412587243)
      ·
        refine ⟨51541924249400642118880865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34361282832933761412587243 51541924249400642118880865)
        ·
          refine ⟨38656443187050481589160649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51541924249400642118880865 38656443187050481589160649)
          ·
            refine ⟨28992332390287861191870487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38656443187050481589160649 28992332390287861191870487)
            ·
              refine ⟨43488498585431791787805731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28992332390287861191870487 43488498585431791787805731)
              ·
                refine ⟨65232747878147687681708597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43488498585431791787805731 65232747878147687681708597)
                ·
                  refine ⟨6115570113576345720160181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65232747878147687681708597 6115570113576345720160181)
                  ·
                    refine ⟨573334698147782411265017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6115570113576345720160181 573334698147782411265017)
                    ·
                      refine ⟨430001023610836808448763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573334698147782411265017 430001023610836808448763)
                      ·
                        rfl

theorem cell23_837424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 5, 5, 2].length) (baseStart_837424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837424 prefixEnd_837424 := by exact prefixLift 837424
  have htrace : WordTrace (prefixWord ++ tailWord_837424) baseStart_837424 baseEnd_837424 := by
    simpa [prefixWord, tailWord_837424, baseEnd_837424] using wordTrace_append hprefix tailTrace_837424
  have hstable : (prefixWord ++ tailWord_837424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837424).length < 2 ^ (prefixWord ++ tailWord_837424).sum := by decide
  have hdescent : baseEnd_837424 < baseStart_837424 := by decide
  rcases family_descends (prefixWord ++ tailWord_837424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837425 : List Nat := [1, 2, 2, 3, 2, 4, 2, 2, 1, 4]
def baseStart_837425 : Nat := 118140960795 + 837425 * 2 ^ 59
def prefixEnd_837425 : Nat := 4983230072969 + 3 ^ 40 * 837425 * 2
def baseEnd_837425 : Nat := 143333845697163768178753

theorem tailTrace_837425 : CollatzResearch.WordTrace tailWord_837425 prefixEnd_837425 143333845697163768178753 := by
  unfold tailWord_837425
  simp only [CollatzResearch.WordTrace]
  refine ⟨30543398991159720648641729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20362265994106480432427819 30543398991159720648641729)
  ·
    refine ⟨22907549243369790486481297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30543398991159720648641729 22907549243369790486481297)
    ·
      refine ⟨17180661932527342864860973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22907549243369790486481297 17180661932527342864860973)
      ·
        refine ⟨6442748224697753574322865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17180661932527342864860973 6442748224697753574322865)
        ·
          refine ⟨4832061168523315180742149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6442748224697753574322865 4832061168523315180742149)
          ·
            refine ⟨906011469098121596389153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4832061168523315180742149 906011469098121596389153)
            ·
              refine ⟨679508601823591197291865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906011469098121596389153 679508601823591197291865)
              ·
                refine ⟨509631451367693397968899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679508601823591197291865 509631451367693397968899)
                ·
                  refine ⟨764447177051540096953349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509631451367693397968899 764447177051540096953349)
                  ·
                    refine ⟨143333845697163768178753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 764447177051540096953349 143333845697163768178753)
                    ·
                      rfl

theorem cell23_837425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_837425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837425 prefixEnd_837425 := by exact prefixLift 837425
  have htrace : WordTrace (prefixWord ++ tailWord_837425) baseStart_837425 baseEnd_837425 := by
    simpa [prefixWord, tailWord_837425, baseEnd_837425] using wordTrace_append hprefix tailTrace_837425
  have hstable : (prefixWord ++ tailWord_837425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837425).length < 2 ^ (prefixWord ++ tailWord_837425).sum := by decide
  have hdescent : baseEnd_837425 < baseStart_837425 := by decide
  rcases family_descends (prefixWord ++ tailWord_837425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837434 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 3, 5]
def baseStart_837434 : Nat := 118140960795 + 837434 * 2 ^ 59
def prefixEnd_837434 : Nat := 4983230072969 + 3 ^ 40 * 837434 * 2
def baseEnd_837434 : Nat := 143335386139127256441239

theorem tailTrace_837434 : CollatzResearch.WordTrace tailWord_837434 prefixEnd_837434 143335386139127256441239 := by
  unfold tailWord_837434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7635931812031778796429839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20362484832084743457146237 7635931812031778796429839)
  ·
    refine ⟨11453897718047668194644759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7635931812031778796429839 11453897718047668194644759)
    ·
      refine ⟨17180846577071502291967139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11453897718047668194644759 17180846577071502291967139)
      ·
        refine ⟨25771269865607253437950709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17180846577071502291967139 25771269865607253437950709)
        ·
          refine ⟨2416056549900680009807879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25771269865607253437950709 2416056549900680009807879)
          ·
            refine ⟨3624084824851020014711819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416056549900680009807879 3624084824851020014711819)
            ·
              refine ⟨5436127237276530022067729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624084824851020014711819 5436127237276530022067729)
              ·
                refine ⟨4077095427957397516550797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5436127237276530022067729 4077095427957397516550797)
                ·
                  refine ⟨1528910785484024068706549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4077095427957397516550797 1528910785484024068706549)
                  ·
                    refine ⟨143335386139127256441239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1528910785484024068706549 143335386139127256441239)
                    ·
                      rfl

theorem cell23_837434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_837434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837434 prefixEnd_837434 := by exact prefixLift 837434
  have htrace : WordTrace (prefixWord ++ tailWord_837434) baseStart_837434 baseEnd_837434 := by
    simpa [prefixWord, tailWord_837434, baseEnd_837434] using wordTrace_append hprefix tailTrace_837434
  have hstable : (prefixWord ++ tailWord_837434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837434).length < 2 ^ (prefixWord ++ tailWord_837434).sum := by decide
  have hdescent : baseEnd_837434 < baseStart_837434 := by decide
  rcases family_descends (prefixWord ++ tailWord_837434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837458 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_837458 : Nat := 118140960795 + 837458 * 2 ^ 59
def prefixEnd_837458 : Nat := 4983230072969 + 3 ^ 40 * 837458 * 2
def baseEnd_837458 : Nat := 430018481953089675423607

theorem tailTrace_837458 : CollatzResearch.WordTrace tailWord_837458 prefixEnd_837458 430018481953089675423607 := by
  unfold tailWord_837458
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636150650010041821148257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20363068400026778189728685 7636150650010041821148257)
  ·
    refine ⟨5727112987507531365861193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7636150650010041821148257 5727112987507531365861193)
    ·
      refine ⟨4295334740630648524395895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5727112987507531365861193 4295334740630648524395895)
      ·
        refine ⟨6443002110945972786593843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4295334740630648524395895 6443002110945972786593843)
        ·
          refine ⟨9664503166418959179890765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6443002110945972786593843 9664503166418959179890765)
          ·
            refine ⟨3624188687407109692459037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9664503166418959179890765 3624188687407109692459037)
            ·
              refine ⟨1359070757777666134672139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3624188687407109692459037 1359070757777666134672139)
              ·
                refine ⟨2038606136666499202008209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359070757777666134672139 2038606136666499202008209)
                ·
                  refine ⟨1528954602499874401506157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2038606136666499202008209 1528954602499874401506157)
                  ·
                    refine ⟨573357975937452900564809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1528954602499874401506157 573357975937452900564809)
                    ·
                      refine ⟨430018481953089675423607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573357975937452900564809 430018481953089675423607)
                      ·
                        rfl

theorem cell23_837458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_837458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837458 prefixEnd_837458 := by exact prefixLift 837458
  have htrace : WordTrace (prefixWord ++ tailWord_837458) baseStart_837458 baseEnd_837458 := by
    simpa [prefixWord, tailWord_837458, baseEnd_837458] using wordTrace_append hprefix tailTrace_837458
  have hstable : (prefixWord ++ tailWord_837458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837458).length < 2 ^ (prefixWord ++ tailWord_837458).sum := by decide
  have hdescent : baseEnd_837458 < baseStart_837458 := by decide
  rcases family_descends (prefixWord ++ tailWord_837458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837468 : List Nat := [2, 2, 4, 2, 2, 1, 1, 3, 1, 5]
def baseStart_837468 : Nat := 118140960795 + 837468 * 2 ^ 59
def prefixEnd_837468 : Nat := 4983230072969 + 3 ^ 40 * 837468 * 2
def baseEnd_837468 : Nat := 143341205586544878766187

theorem tailTrace_837468 : CollatzResearch.WordTrace tailWord_837468 prefixEnd_837468 143341205586544878766187 := by
  unfold tailWord_837468
  simp only [CollatzResearch.WordTrace]
  refine ⟨15272483665001969496228529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20363311553335959328304705 15272483665001969496228529)
  ·
    refine ⟨11454362748751477122171397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15272483665001969496228529 11454362748751477122171397)
    ·
      refine ⟨2147693015390901960407137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11454362748751477122171397 2147693015390901960407137)
      ·
        refine ⟨1610769761543176470305353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2147693015390901960407137 1610769761543176470305353)
        ·
          refine ⟨1208077321157382352729015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1610769761543176470305353 1208077321157382352729015)
          ·
            refine ⟨1812115981736073529093523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208077321157382352729015 1812115981736073529093523)
            ·
              refine ⟨2718173972604110293640285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812115981736073529093523 2718173972604110293640285)
              ·
                refine ⟨1019315239726541360115107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2718173972604110293640285 1019315239726541360115107)
                ·
                  refine ⟨1528972859589812040172661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019315239726541360115107 1528972859589812040172661)
                  ·
                    refine ⟨143341205586544878766187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1528972859589812040172661 143341205586544878766187)
                    ·
                      rfl

theorem cell23_837468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_837468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837468 prefixEnd_837468 := by exact prefixLift 837468
  have htrace : WordTrace (prefixWord ++ tailWord_837468) baseStart_837468 baseEnd_837468 := by
    simpa [prefixWord, tailWord_837468, baseEnd_837468] using wordTrace_append hprefix tailTrace_837468
  have hstable : (prefixWord ++ tailWord_837468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837468).length < 2 ^ (prefixWord ++ tailWord_837468).sum := by decide
  have hdescent : baseEnd_837468 < baseStart_837468 := by decide
  rcases family_descends (prefixWord ++ tailWord_837468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837471 : List Nat := [1, 1, 2, 3, 1, 5, 1, 3, 1, 1, 4]
def baseStart_837471 : Nat := 118140960795 + 837471 * 2 ^ 59
def prefixEnd_837471 : Nat := 4983230072969 + 3 ^ 40 * 837471 * 2
def baseEnd_837471 : Nat := 430025157201598124561047

theorem tailTrace_837471 : CollatzResearch.WordTrace tailWord_837471 prefixEnd_837471 430025157201598124561047 := by
  unfold tailWord_837471
  simp only [CollatzResearch.WordTrace]
  refine ⟨30545076748993070504816267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20363384499328713669877511 30545076748993070504816267)
  ·
    refine ⟨45817615123489605757224401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30545076748993070504816267 45817615123489605757224401)
    ·
      refine ⟨34363211342617204317918301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45817615123489605757224401 34363211342617204317918301)
      ·
        refine ⟨12886204253481451619219363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34363211342617204317918301 12886204253481451619219363)
        ·
          refine ⟨19329306380222177428829045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12886204253481451619219363 19329306380222177428829045)
          ·
            refine ⟨1812122473145829133952723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19329306380222177428829045 1812122473145829133952723)
            ·
              refine ⟨2718183709718743700929085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812122473145829133952723 2718183709718743700929085)
              ·
                refine ⟨1019318891144528887848407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2718183709718743700929085 1019318891144528887848407)
                ·
                  refine ⟨1528978336716793331772611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019318891144528887848407 1528978336716793331772611)
                  ·
                    refine ⟨2293467505075189997658917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1528978336716793331772611 2293467505075189997658917)
                    ·
                      refine ⟨430025157201598124561047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2293467505075189997658917 430025157201598124561047)
                      ·
                        rfl

theorem cell23_837471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_837471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837471 prefixEnd_837471 := by exact prefixLift 837471
  have htrace : WordTrace (prefixWord ++ tailWord_837471) baseStart_837471 baseEnd_837471 := by
    simpa [prefixWord, tailWord_837471, baseEnd_837471] using wordTrace_append hprefix tailTrace_837471
  have hstable : (prefixWord ++ tailWord_837471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837471).length < 2 ^ (prefixWord ++ tailWord_837471).sum := by decide
  have hdescent : baseEnd_837471 < baseStart_837471 := by decide
  rcases family_descends (prefixWord ++ tailWord_837471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837487 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 7]
def baseStart_837487 : Nat := 118140960795 + 837487 * 2 ^ 59
def prefixEnd_837487 : Nat := 4983230072969 + 3 ^ 40 * 837487 * 2
def baseEnd_837487 : Nat := 430033372892070061960973

theorem tailTrace_837487 : CollatzResearch.WordTrace tailWord_837487 prefixEnd_837487 430033372892070061960973 := by
  unfold tailWord_837487
  simp only [CollatzResearch.WordTrace]
  refine ⟨30545660316935105237398715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20363773544623403491599143 30545660316935105237398715)
  ·
    refine ⟨45818490475402657856098073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30545660316935105237398715 45818490475402657856098073)
    ·
      refine ⟨34363867856551993392073555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45818490475402657856098073 34363867856551993392073555)
      ·
        refine ⟨51545801784827990088110333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34363867856551993392073555 51545801784827990088110333)
        ·
          refine ⟨19329675669310496283041375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51545801784827990088110333 19329675669310496283041375)
          ·
            refine ⟨28994513503965744424562063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19329675669310496283041375 28994513503965744424562063)
            ·
              refine ⟨43491770255948616636843095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28994513503965744424562063 43491770255948616636843095)
              ·
                refine ⟨65237655383922924955264643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43491770255948616636843095 65237655383922924955264643)
                ·
                  refine ⟨97856483075884387432896965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65237655383922924955264643 97856483075884387432896965)
                  ·
                    refine ⟨18348090576728322643668181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97856483075884387432896965 18348090576728322643668181)
                    ·
                      refine ⟨430033372892070061960973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18348090576728322643668181 430033372892070061960973)
                      ·
                        rfl

theorem cell23_837487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_837487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837487 prefixEnd_837487 := by exact prefixLift 837487
  have htrace : WordTrace (prefixWord ++ tailWord_837487) baseStart_837487 baseEnd_837487 := by
    simpa [prefixWord, tailWord_837487, baseEnd_837487] using wordTrace_append hprefix tailTrace_837487
  have hstable : (prefixWord ++ tailWord_837487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837487).length < 2 ^ (prefixWord ++ tailWord_837487).sum := by decide
  have hdescent : baseEnd_837487 < baseStart_837487 := by decide
  rcases family_descends (prefixWord ++ tailWord_837487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837505 : List Nat := [1, 2, 4, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_837505 : Nat := 118140960795 + 837505 * 2 ^ 59
def prefixEnd_837505 : Nat := 4983230072969 + 3 ^ 40 * 837505 * 2
def baseEnd_837505 : Nat := 430042615543850991535891

theorem tailTrace_837505 : CollatzResearch.WordTrace tailWord_837505 prefixEnd_837505 430042615543850991535891 := by
  unfold tailWord_837505
  simp only [CollatzResearch.WordTrace]
  refine ⟨30546316830869894311553969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20364211220579929541035979 30546316830869894311553969)
  ·
    refine ⟨22909737623152420733665477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30546316830869894311553969 22909737623152420733665477)
    ·
      refine ⟨4295575804341078887562277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22909737623152420733665477 4295575804341078887562277)
      ·
        refine ⟨805420463313952291417927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4295575804341078887562277 805420463313952291417927)
        ·
          refine ⟨1208130694970928437126891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805420463313952291417927 1208130694970928437126891)
          ·
            refine ⟨1812196042456392655690337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208130694970928437126891 1812196042456392655690337)
            ·
              refine ⟨1359147031842294491767753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812196042456392655690337 1359147031842294491767753)
              ·
                refine ⟨1019360273881720868825815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359147031842294491767753 1019360273881720868825815)
                ·
                  refine ⟨1529040410822581303238723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019360273881720868825815 1529040410822581303238723)
                  ·
                    refine ⟨2293560616233871954858085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1529040410822581303238723 2293560616233871954858085)
                    ·
                      refine ⟨430042615543850991535891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2293560616233871954858085 430042615543850991535891)
                      ·
                        rfl

theorem cell23_837505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_837505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837505 prefixEnd_837505 := by exact prefixLift 837505
  have htrace : WordTrace (prefixWord ++ tailWord_837505) baseStart_837505 baseEnd_837505 := by
    simpa [prefixWord, tailWord_837505, baseEnd_837505] using wordTrace_append hprefix tailTrace_837505
  have hstable : (prefixWord ++ tailWord_837505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837505).length < 2 ^ (prefixWord ++ tailWord_837505).sum := by decide
  have hdescent : baseEnd_837505 < baseStart_837505 := by decide
  rcases family_descends (prefixWord ++ tailWord_837505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837521 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 4, 1, 3]
def baseStart_837521 : Nat := 118140960795 + 837521 * 2 ^ 59
def prefixEnd_837521 : Nat := 4983230072969 + 3 ^ 40 * 837521 * 2
def baseEnd_837521 : Nat := 430050831234322928935817

theorem tailTrace_837521 : CollatzResearch.WordTrace tailWord_837521 prefixEnd_837521 430050831234322928935817 := by
  unfold tailWord_837521
  simp only [CollatzResearch.WordTrace]
  refine ⟨30546900398811929044136417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20364600265874619362757611 30546900398811929044136417)
  ·
    refine ⟨22910175299108946783102313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30546900398811929044136417 22910175299108946783102313)
    ·
      refine ⟨17182631474331710087326735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22910175299108946783102313 17182631474331710087326735)
      ·
        refine ⟨25773947211497565130990103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17182631474331710087326735 25773947211497565130990103)
        ·
          refine ⟨38660920817246347696485155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25773947211497565130990103 38660920817246347696485155)
          ·
            refine ⟨57991381225869521544727733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38660920817246347696485155 57991381225869521544727733)
            ·
              refine ⟨5436691989925267644818225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57991381225869521544727733 5436691989925267644818225)
              ·
                refine ⟨4077518992443950733613669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5436691989925267644818225 4077518992443950733613669)
                ·
                  refine ⟨764534811083240762552563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4077518992443950733613669 764534811083240762552563)
                  ·
                    refine ⟨1146802216624861143828845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 764534811083240762552563 1146802216624861143828845)
                    ·
                      refine ⟨430050831234322928935817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1146802216624861143828845 430050831234322928935817)
                      ·
                        rfl

theorem cell23_837521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_837521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837521 prefixEnd_837521 := by exact prefixLift 837521
  have htrace : WordTrace (prefixWord ++ tailWord_837521) baseStart_837521 baseEnd_837521 := by
    simpa [prefixWord, tailWord_837521, baseEnd_837521] using wordTrace_append hprefix tailTrace_837521
  have hstable : (prefixWord ++ tailWord_837521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837521).length < 2 ^ (prefixWord ++ tailWord_837521).sum := by decide
  have hdescent : baseEnd_837521 < baseStart_837521 := by decide
  rcases family_descends (prefixWord ++ tailWord_837521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837528 : List Nat := [2, 1, 2, 6, 2, 1, 9]
def baseStart_837528 : Nat := 118140960795 + 837528 * 2 ^ 59
def prefixEnd_837528 : Nat := 4983230072969 + 3 ^ 40 * 837528 * 2
def baseEnd_837528 : Nat := 5309313896282770389485

theorem tailTrace_837528 : CollatzResearch.WordTrace tailWord_837528 prefixEnd_837528 5309313896282770389485 := by
  unfold tailWord_837528
  simp only [CollatzResearch.WordTrace]
  refine ⟨15273577854893284619820619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20364770473191046159760825 15273577854893284619820619)
  ·
    refine ⟨22910366782339926929730929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15273577854893284619820619 22910366782339926929730929)
    ·
      refine ⟨17182775086754945197298197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22910366782339926929730929 17182775086754945197298197)
      ·
        refine ⟨805442582191638056123353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17182775086754945197298197 805442582191638056123353)
        ·
          refine ⟨604081936643728542092515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 805442582191638056123353 604081936643728542092515)
          ·
            refine ⟨906122904965592813138773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604081936643728542092515 906122904965592813138773)
            ·
              refine ⟨5309313896282770389485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 906122904965592813138773 5309313896282770389485)
              ·
                rfl

theorem cell23_837528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 9].length) (baseStart_837528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837528 prefixEnd_837528 := by exact prefixLift 837528
  have htrace : WordTrace (prefixWord ++ tailWord_837528) baseStart_837528 baseEnd_837528 := by
    simpa [prefixWord, tailWord_837528, baseEnd_837528] using wordTrace_append hprefix tailTrace_837528
  have hstable : (prefixWord ++ tailWord_837528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837528).length < 2 ^ (prefixWord ++ tailWord_837528).sum := by decide
  have hdescent : baseEnd_837528 < baseStart_837528 := by decide
  rcases family_descends (prefixWord ++ tailWord_837528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837554 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_837554 : Nat := 118140960795 + 837554 * 2 ^ 59
def prefixEnd_837554 : Nat := 4983230072969 + 3 ^ 40 * 837554 * 2
def baseEnd_837554 : Nat := 143355925365307099941055

theorem tailTrace_837554 : CollatzResearch.WordTrace tailWord_837554 prefixEnd_837554 143355925365307099941055 := by
  unfold tailWord_837554
  simp only [CollatzResearch.WordTrace]
  refine ⟨7637026001923093920021929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20365402671794917120058477 7637026001923093920021929)
  ·
    refine ⟨5727769501442320440016447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7637026001923093920021929 5727769501442320440016447)
    ·
      refine ⟨8591654252163480660024671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5727769501442320440016447 8591654252163480660024671)
      ·
        refine ⟨12887481378245220990037007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8591654252163480660024671 12887481378245220990037007)
        ·
          refine ⟨19331222067367831485055511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12887481378245220990037007 19331222067367831485055511)
          ·
            refine ⟨28996833101051747227583267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19331222067367831485055511 28996833101051747227583267)
            ·
              refine ⟨43495249651577620841374901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28996833101051747227583267 43495249651577620841374901)
              ·
                refine ⟨4077679654835401953878897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43495249651577620841374901 4077679654835401953878897)
                ·
                  refine ⟨3058259741126551465409173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4077679654835401953878897 3058259741126551465409173)
                  ·
                    refine ⟨143355925365307099941055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3058259741126551465409173 143355925365307099941055)
                    ·
                      rfl

theorem cell23_837554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_837554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837554 prefixEnd_837554 := by exact prefixLift 837554
  have htrace : WordTrace (prefixWord ++ tailWord_837554) baseStart_837554 baseEnd_837554 := by
    simpa [prefixWord, tailWord_837554, baseEnd_837554] using wordTrace_append hprefix tailTrace_837554
  have hstable : (prefixWord ++ tailWord_837554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837554).length < 2 ^ (prefixWord ++ tailWord_837554).sum := by decide
  have hdescent : baseEnd_837554 < baseStart_837554 := by decide
  rcases family_descends (prefixWord ++ tailWord_837554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837565 : List Nat := [1, 4, 1, 2, 3, 1, 3, 2, 1, 3, 2]
def baseStart_837565 : Nat := 118140960795 + 837565 * 2 ^ 59
def prefixEnd_837565 : Nat := 4983230072969 + 3 ^ 40 * 837565 * 2
def baseEnd_837565 : Nat := 430073424383120756785615

theorem tailTrace_837565 : CollatzResearch.WordTrace tailWord_837565 prefixEnd_837565 430073424383120756785615 := by
  unfold tailWord_837565
  simp only [CollatzResearch.WordTrace]
  refine ⟨30548505210652524558738149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20365670140435016372492099 30548505210652524558738149)
  ·
    refine ⟨5727844726997348354763403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30548505210652524558738149 5727844726997348354763403)
    ·
      refine ⟨8591767090496022532145105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5727844726997348354763403 8591767090496022532145105)
      ·
        refine ⟨6443825317872016899108829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8591767090496022532145105 6443825317872016899108829)
        ·
          refine ⟨2416434494202006337165811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6443825317872016899108829 2416434494202006337165811)
          ·
            refine ⟨3624651741303009505748717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416434494202006337165811 3624651741303009505748717)
            ·
              refine ⟨1359244402988628564655769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3624651741303009505748717 1359244402988628564655769)
              ·
                refine ⟨1019433302241471423491827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359244402988628564655769 1019433302241471423491827)
                ·
                  refine ⟨1529149953362207135237741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019433302241471423491827 1529149953362207135237741)
                  ·
                    refine ⟨573431232510827675714153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1529149953362207135237741 573431232510827675714153)
                    ·
                      refine ⟨430073424383120756785615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573431232510827675714153 430073424383120756785615)
                      ·
                        rfl

theorem cell23_837565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_837565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837565 prefixEnd_837565 := by exact prefixLift 837565
  have htrace : WordTrace (prefixWord ++ tailWord_837565) baseStart_837565 baseEnd_837565 := by
    simpa [prefixWord, tailWord_837565, baseEnd_837565] using wordTrace_append hprefix tailTrace_837565
  have hstable : (prefixWord ++ tailWord_837565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837565).length < 2 ^ (prefixWord ++ tailWord_837565).sum := by decide
  have hdescent : baseEnd_837565 < baseStart_837565 := by decide
  rcases family_descends (prefixWord ++ tailWord_837565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837578 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 6, 2, 2]
def baseStart_837578 : Nat := 118140960795 + 837578 * 2 ^ 59
def prefixEnd_837578 : Nat := 4983230072969 + 3 ^ 40 * 837578 * 2
def baseEnd_837578 : Nat := 430080099631629205923055

theorem tailTrace_837578 : CollatzResearch.WordTrace tailWord_837578 prefixEnd_837578 430080099631629205923055 := by
  unfold tailWord_837578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7637244839901356944740347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20365986239736951852640925 7637244839901356944740347)
  ·
    refine ⟨11455867259852035417110521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7637244839901356944740347 11455867259852035417110521)
    ·
      refine ⟨8591900444889026562832891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11455867259852035417110521 8591900444889026562832891)
      ·
        refine ⟨12887850667333539844249337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8591900444889026562832891 12887850667333539844249337)
        ·
          refine ⟨9665888000500154883187003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12887850667333539844249337 9665888000500154883187003)
          ·
            refine ⟨14498832000750232324780505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9665888000500154883187003 14498832000750232324780505)
            ·
              refine ⟨10874124000562674243585379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14498832000750232324780505 10874124000562674243585379)
              ·
                refine ⟨16311186000844011365378069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10874124000562674243585379 16311186000844011365378069)
                ·
                  refine ⟨764586843789563032752097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16311186000844011365378069 764586843789563032752097)
                  ·
                    refine ⟨573440132842172274564073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 764586843789563032752097 573440132842172274564073)
                    ·
                      refine ⟨430080099631629205923055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573440132842172274564073 430080099631629205923055)
                      ·
                        rfl

theorem cell23_837578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_837578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837578 prefixEnd_837578 := by exact prefixLift 837578
  have htrace : WordTrace (prefixWord ++ tailWord_837578) baseStart_837578 baseEnd_837578 := by
    simpa [prefixWord, tailWord_837578, baseEnd_837578] using wordTrace_append hprefix tailTrace_837578
  have hstable : (prefixWord ++ tailWord_837578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837578).length < 2 ^ (prefixWord ++ tailWord_837578).sum := by decide
  have hdescent : baseEnd_837578 < baseStart_837578 := by decide
  rcases family_descends (prefixWord ++ tailWord_837578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837624 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_837624 : Nat := 118140960795 + 837624 * 2 ^ 59
def prefixEnd_837624 : Nat := 4983230072969 + 3 ^ 40 * 837624 * 2
def baseEnd_837624 : Nat := 430103719741736025947843

theorem tailTrace_837624 : CollatzResearch.WordTrace tailWord_837624 prefixEnd_837624 430103719741736025947843 := by
  unfold tailWord_837624
  simp only [CollatzResearch.WordTrace]
  refine ⟨15275328558719388817567963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20367104744959185090090617 15275328558719388817567963)
  ·
    refine ⟨22912992838079083226351945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15275328558719388817567963 22912992838079083226351945)
    ·
      refine ⟨17184744628559312419763959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22912992838079083226351945 17184744628559312419763959)
      ·
        refine ⟨25777116942838968629645939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17184744628559312419763959 25777116942838968629645939)
        ·
          refine ⟨38665675414258452944468909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25777116942838968629645939 38665675414258452944468909)
          ·
            refine ⟨14499628280346919854175841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38665675414258452944468909 14499628280346919854175841)
            ·
              refine ⟨10874721210260189890631881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14499628280346919854175841 10874721210260189890631881)
              ·
                refine ⟨8156040907695142417973911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10874721210260189890631881 8156040907695142417973911)
                ·
                  refine ⟨12234061361542713626960867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8156040907695142417973911 12234061361542713626960867)
                  ·
                    refine ⟨18351092042314070440441301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12234061361542713626960867 18351092042314070440441301)
                    ·
                      refine ⟨430103719741736025947843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 18351092042314070440441301 430103719741736025947843)
                      ·
                        rfl

theorem cell23_837624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_837624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837624 prefixEnd_837624 := by exact prefixLift 837624
  have htrace : WordTrace (prefixWord ++ tailWord_837624) baseStart_837624 baseEnd_837624 := by
    simpa [prefixWord, tailWord_837624, baseEnd_837624] using wordTrace_append hprefix tailTrace_837624
  have hstable : (prefixWord ++ tailWord_837624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837624).length < 2 ^ (prefixWord ++ tailWord_837624).sum := by decide
  have hdescent : baseEnd_837624 < baseStart_837624 := by decide
  rcases family_descends (prefixWord ++ tailWord_837624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837651 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 4]
def baseStart_837651 : Nat := 118140960795 + 837651 * 2 ^ 59
def prefixEnd_837651 : Nat := 4983230072969 + 3 ^ 40 * 837651 * 2
def baseEnd_837651 : Nat := 430117583719407420310219

theorem tailTrace_837651 : CollatzResearch.WordTrace tailWord_837651 prefixEnd_837651 430117583719407420310219 := by
  unfold tailWord_837651
  simp only [CollatzResearch.WordTrace]
  refine ⟨30551641888340961246368807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20367761258893974164245871 30551641888340961246368807)
  ·
    refine ⟨45827462832511441869553211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30551641888340961246368807 45827462832511441869553211)
    ·
      refine ⟨68741194248767162804329817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45827462832511441869553211 68741194248767162804329817)
      ·
        refine ⟨51555895686575372103247363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68741194248767162804329817 51555895686575372103247363)
        ·
          refine ⟨77333843529863058154871045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51555895686575372103247363 77333843529863058154871045)
          ·
            refine ⟨14500095661849323404038321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77333843529863058154871045 14500095661849323404038321)
            ·
              refine ⟨10875071746386992553028741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14500095661849323404038321 10875071746386992553028741)
              ·
                refine ⟨2039075952447561103692889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10875071746386992553028741 2039075952447561103692889)
                ·
                  refine ⟨1529306964335670827769667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2039075952447561103692889 1529306964335670827769667)
                  ·
                    refine ⟨2293960446503506241654501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1529306964335670827769667 2293960446503506241654501)
                    ·
                      refine ⟨430117583719407420310219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2293960446503506241654501 430117583719407420310219)
                      ·
                        rfl

theorem cell23_837651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_837651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837651 prefixEnd_837651 := by exact prefixLift 837651
  have htrace : WordTrace (prefixWord ++ tailWord_837651) baseStart_837651 baseEnd_837651 := by
    simpa [prefixWord, tailWord_837651, baseEnd_837651] using wordTrace_append hprefix tailTrace_837651
  have hstable : (prefixWord ++ tailWord_837651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837651).length < 2 ^ (prefixWord ++ tailWord_837651).sum := by decide
  have hdescent : baseEnd_837651 < baseStart_837651 := by decide
  rcases family_descends (prefixWord ++ tailWord_837651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837695 : List Nat := [1, 1, 2, 2, 3, 1, 5, 3, 1, 4]
def baseStart_837695 : Nat := 118140960795 + 837695 * 2 ^ 59
def prefixEnd_837695 : Nat := 4983230072969 + 3 ^ 40 * 837695 * 2
def baseEnd_837695 : Nat := 143380058956068416053339

theorem tailTrace_837695 : CollatzResearch.WordTrace tailWord_837695 prefixEnd_837695 143380058956068416053339 := by
  unfold tailWord_837695
  simp only [CollatzResearch.WordTrace]
  refine ⟨30553246700181556760970539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20368831133454371173980359 30553246700181556760970539)
  ·
    refine ⟨45829870050272335141455809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30553246700181556760970539 45829870050272335141455809)
    ·
      refine ⟨34372402537704251356091857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45829870050272335141455809 34372402537704251356091857)
      ·
        refine ⟨25779301903278188517068893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34372402537704251356091857 25779301903278188517068893)
        ·
          refine ⟨9667238213729320693900835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25779301903278188517068893 9667238213729320693900835)
          ·
            refine ⟨14500857320593981040851253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9667238213729320693900835 14500857320593981040851253)
            ·
              refine ⟨1359455373805685722579805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14500857320593981040851253 1359455373805685722579805)
              ·
                refine ⟨509795765177132145967427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1359455373805685722579805 509795765177132145967427)
                ·
                  refine ⟨764693647765698218951141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509795765177132145967427 764693647765698218951141)
                  ·
                    refine ⟨143380058956068416053339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 764693647765698218951141 143380058956068416053339)
                    ·
                      rfl

theorem cell23_837695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 1, 4].length) (baseStart_837695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837695 prefixEnd_837695 := by exact prefixLift 837695
  have htrace : WordTrace (prefixWord ++ tailWord_837695) baseStart_837695 baseEnd_837695 := by
    simpa [prefixWord, tailWord_837695, baseEnd_837695] using wordTrace_append hprefix tailTrace_837695
  have hstable : (prefixWord ++ tailWord_837695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837695).length < 2 ^ (prefixWord ++ tailWord_837695).sum := by decide
  have hdescent : baseEnd_837695 < baseStart_837695 := by decide
  rcases family_descends (prefixWord ++ tailWord_837695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837721 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 3, 5]
def baseStart_837721 : Nat := 118140960795 + 837721 * 2 ^ 59
def prefixEnd_837721 : Nat := 4983230072969 + 3 ^ 40 * 837721 * 2
def baseEnd_837721 : Nat := 143384509121740715478299

theorem tailTrace_837721 : CollatzResearch.WordTrace tailWord_837721 prefixEnd_837721 143384509121740715478299 := by
  unfold tailWord_837721
  simp only [CollatzResearch.WordTrace]
  refine ⟨30554194998087363201417017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20369463332058242134278011 30554194998087363201417017)
  ·
    refine ⟨22915646248565522401062763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30554194998087363201417017 22915646248565522401062763)
    ·
      refine ⟨34373469372848283601594145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22915646248565522401062763 34373469372848283601594145)
      ·
        refine ⟨25780102029636212701195609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34373469372848283601594145 25780102029636212701195609)
        ·
          refine ⟨19335076522227159525896707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25780102029636212701195609 19335076522227159525896707)
          ·
            refine ⟨29002614783340739288845061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19335076522227159525896707 29002614783340739288845061)
            ·
              refine ⟨5437990271876388616658449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29002614783340739288845061 5437990271876388616658449)
              ·
                refine ⟨4078492703907291462493837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5437990271876388616658449 4078492703907291462493837)
                ·
                  refine ⟨1529434763965234298435189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4078492703907291462493837 1529434763965234298435189)
                  ·
                    refine ⟨143384509121740715478299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1529434763965234298435189 143384509121740715478299)
                    ·
                      rfl

theorem cell23_837721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 5].length) (baseStart_837721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837721 prefixEnd_837721 := by exact prefixLift 837721
  have htrace : WordTrace (prefixWord ++ tailWord_837721) baseStart_837721 baseEnd_837721 := by
    simpa [prefixWord, tailWord_837721, baseEnd_837721] using wordTrace_append hprefix tailTrace_837721
  have hstable : (prefixWord ++ tailWord_837721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837721).length < 2 ^ (prefixWord ++ tailWord_837721).sum := by decide
  have hdescent : baseEnd_837721 < baseStart_837721 := by decide
  rcases family_descends (prefixWord ++ tailWord_837721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837725 : List Nat := [1, 4, 4, 1, 1, 2, 1, 3, 6]
def baseStart_837725 : Nat := 118140960795 + 837725 * 2 ^ 59
def prefixEnd_837725 : Nat := 4983230072969 + 3 ^ 40 * 837725 * 2
def baseEnd_837725 : Nat := 47795064587537792309431

theorem tailTrace_837725 : CollatzResearch.WordTrace tailWord_837725 prefixEnd_837725 47795064587537792309431 := by
  unfold tailWord_837725
  simp only [CollatzResearch.WordTrace]
  refine ⟨30554340890072871884562629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20369560593381914589708419 30554340890072871884562629)
  ·
    refine ⟨5728938916888663478355493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30554340890072871884562629 5728938916888663478355493)
    ·
      refine ⟨1074176046916624402191655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5728938916888663478355493 1074176046916624402191655)
      ·
        refine ⟨1611264070374936603287483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074176046916624402191655 1611264070374936603287483)
        ·
          refine ⟨2416896105562404904931225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611264070374936603287483 2416896105562404904931225)
          ·
            refine ⟨1812672079171803678698419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2416896105562404904931225 1812672079171803678698419)
            ·
              refine ⟨2719008118757705518047629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812672079171803678698419 2719008118757705518047629)
              ·
                refine ⟨1019628044534139569267861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2719008118757705518047629 1019628044534139569267861)
                ·
                  refine ⟨47795064587537792309431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1019628044534139569267861 47795064587537792309431)
                  ·
                    rfl

theorem cell23_837725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_837725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837725 prefixEnd_837725 := by exact prefixLift 837725
  have htrace : WordTrace (prefixWord ++ tailWord_837725) baseStart_837725 baseEnd_837725 := by
    simpa [prefixWord, tailWord_837725, baseEnd_837725] using wordTrace_append hprefix tailTrace_837725
  have hstable : (prefixWord ++ tailWord_837725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837725).length < 2 ^ (prefixWord ++ tailWord_837725).sum := by decide
  have hdescent : baseEnd_837725 < baseStart_837725 := by decide
  rcases family_descends (prefixWord ++ tailWord_837725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837745 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 2, 3, 2]
def baseStart_837745 : Nat := 118140960795 + 837745 * 2 ^ 59
def prefixEnd_837745 : Nat := 4983230072969 + 3 ^ 40 * 837745 * 2
def baseEnd_837745 : Nat := 430165850900930052534787

theorem tailTrace_837745 : CollatzResearch.WordTrace tailWord_837745 prefixEnd_837745 430165850900930052534787 := by
  unfold tailWord_837745
  simp only [CollatzResearch.WordTrace]
  refine ⟨30555070350000415300290689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20370046900000276866860459 30555070350000415300290689)
  ·
    refine ⟨22916302762500311475218017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30555070350000415300290689 22916302762500311475218017)
    ·
      refine ⟨17187227071875233606413513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22916302762500311475218017 17187227071875233606413513)
      ·
        refine ⟨12890420303906425204810135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17187227071875233606413513 12890420303906425204810135)
        ·
          refine ⟨19335630455859637807215203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12890420303906425204810135 19335630455859637807215203)
          ·
            refine ⟨29003445683789456710822805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19335630455859637807215203 29003445683789456710822805)
            ·
              refine ⟨1359536516427630783319819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29003445683789456710822805 1359536516427630783319819)
              ·
                refine ⟨2039304774641446174979729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359536516427630783319819 2039304774641446174979729)
                ·
                  refine ⟨1529478580981084631234797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2039304774641446174979729 1529478580981084631234797)
                  ·
                    refine ⟨573554467867906736713049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1529478580981084631234797 573554467867906736713049)
                    ·
                      refine ⟨430165850900930052534787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573554467867906736713049 430165850900930052534787)
                      ·
                        rfl

theorem cell23_837745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_837745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837745 prefixEnd_837745 := by exact prefixLift 837745
  have htrace : WordTrace (prefixWord ++ tailWord_837745) baseStart_837745 baseEnd_837745 := by
    simpa [prefixWord, tailWord_837745, baseEnd_837745] using wordTrace_append hprefix tailTrace_837745
  have hstable : (prefixWord ++ tailWord_837745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837745).length < 2 ^ (prefixWord ++ tailWord_837745).sum := by decide
  have hdescent : baseEnd_837745 < baseStart_837745 := by decide
  rcases family_descends (prefixWord ++ tailWord_837745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837751 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 3, 6]
def baseStart_837751 : Nat := 118140960795 + 837751 * 2 ^ 59
def prefixEnd_837751 : Nat := 4983230072969 + 3 ^ 40 * 837751 * 2
def baseEnd_837751 : Nat := 143389643928285676353253

theorem tailTrace_837751 : CollatzResearch.WordTrace tailWord_837751 prefixEnd_837751 143389643928285676353253 := by
  unfold tailWord_837751
  simp only [CollatzResearch.WordTrace]
  refine ⟨30555289187978678325009107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20370192791985785550006071 30555289187978678325009107)
  ·
    refine ⟨45832933781968017487513661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30555289187978678325009107 45832933781968017487513661)
    ·
      refine ⟨17187350168238006557817623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45832933781968017487513661 17187350168238006557817623)
      ·
        refine ⟨25781025252357009836726435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17187350168238006557817623 25781025252357009836726435)
        ·
          refine ⟨38671537878535514755089653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25781025252357009836726435 38671537878535514755089653)
          ·
            refine ⟨3625456676112704508289655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38671537878535514755089653 3625456676112704508289655)
            ·
              refine ⟨5438185014169056762434483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3625456676112704508289655 5438185014169056762434483)
              ·
                refine ⟨8157277521253585143651725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5438185014169056762434483 8157277521253585143651725)
                ·
                  refine ⟨3058979070470094428869397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8157277521253585143651725 3058979070470094428869397)
                  ·
                    refine ⟨143389643928285676353253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3058979070470094428869397 143389643928285676353253)
                    ·
                      rfl

theorem cell23_837751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_837751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837751 prefixEnd_837751 := by exact prefixLift 837751
  have htrace : WordTrace (prefixWord ++ tailWord_837751) baseStart_837751 baseEnd_837751 := by
    simpa [prefixWord, tailWord_837751, baseEnd_837751] using wordTrace_append hprefix tailTrace_837751
  have hstable : (prefixWord ++ tailWord_837751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837751).length < 2 ^ (prefixWord ++ tailWord_837751).sum := by decide
  have hdescent : baseEnd_837751 < baseStart_837751 := by decide
  rcases family_descends (prefixWord ++ tailWord_837751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837778 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_837778 : Nat := 118140960795 + 837778 * 2 ^ 59
def prefixEnd_837778 : Nat := 4983230072969 + 3 ^ 40 * 837778 * 2
def baseEnd_837778 : Nat := 430182795762528423422135

theorem tailTrace_837778 : CollatzResearch.WordTrace tailWord_837778 prefixEnd_837778 430182795762528423422135 := by
  unfold tailWord_837778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7639068489720215484060497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20370849305920574624161325 7639068489720215484060497)
  ·
    refine ⟨5729301367290161613045373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7639068489720215484060497 5729301367290161613045373)
    ·
      refine ⟨2148488012733810604892015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5729301367290161613045373 2148488012733810604892015)
      ·
        refine ⟨3222732019100715907338023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2148488012733810604892015 3222732019100715907338023)
        ·
          refine ⟨4834098028651073861007035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3222732019100715907338023 4834098028651073861007035)
          ·
            refine ⟨7251147042976610791510553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4834098028651073861007035 7251147042976610791510553)
            ·
              refine ⟨5438360282232458093632915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7251147042976610791510553 5438360282232458093632915)
              ·
                refine ⟨8157540423348687140449373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5438360282232458093632915 8157540423348687140449373)
                ·
                  refine ⟨3059077658755757677668515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8157540423348687140449373 3059077658755757677668515)
                  ·
                    refine ⟨4588616488133636516502773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3059077658755757677668515 4588616488133636516502773)
                    ·
                      refine ⟨430182795762528423422135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4588616488133636516502773 430182795762528423422135)
                      ·
                        rfl

theorem cell23_837778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_837778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837778 prefixEnd_837778 := by exact prefixLift 837778
  have htrace : WordTrace (prefixWord ++ tailWord_837778) baseStart_837778 baseEnd_837778 := by
    simpa [prefixWord, tailWord_837778, baseEnd_837778] using wordTrace_append hprefix tailTrace_837778
  have hstable : (prefixWord ++ tailWord_837778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837778).length < 2 ^ (prefixWord ++ tailWord_837778).sum := by decide
  have hdescent : baseEnd_837778 < baseStart_837778 := by decide
  rcases family_descends (prefixWord ++ tailWord_837778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837792 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 3, 2, 2]
def baseStart_837792 : Nat := 118140960795 + 837792 * 2 ^ 59
def prefixEnd_837792 : Nat := 4983230072969 + 3 ^ 40 * 837792 * 2
def baseEnd_837792 : Nat := 430189984491691368647071

theorem tailTrace_837792 : CollatzResearch.WordTrace tailWord_837792 prefixEnd_837792 430189984491691368647071 := by
  unfold tailWord_837792
  simp only [CollatzResearch.WordTrace]
  refine ⟨15278392290415071163625815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20371189720553428218167753 15278392290415071163625815)
  ·
    refine ⟨22917588435622606745438723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15278392290415071163625815 22917588435622606745438723)
    ·
      refine ⟨34376382653433910118158085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22917588435622606745438723 34376382653433910118158085)
      ·
        refine ⟨6445571747518858147154641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34376382653433910118158085 6445571747518858147154641)
        ·
          refine ⟨4834178810639143610365981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6445571747518858147154641 4834178810639143610365981)
          ·
            refine ⟨1812817053989678853887243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4834178810639143610365981 1812817053989678853887243)
            ·
              refine ⟨2719225580984518280830865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812817053989678853887243 2719225580984518280830865)
              ·
                refine ⟨2039419185738388710623149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2719225580984518280830865 2039419185738388710623149)
                ·
                  refine ⟨764782194651895766483681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2039419185738388710623149 764782194651895766483681)
                  ·
                    refine ⟨573586645988921824862761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 764782194651895766483681 573586645988921824862761)
                    ·
                      refine ⟨430189984491691368647071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573586645988921824862761 430189984491691368647071)
                      ·
                        rfl

theorem cell23_837792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_837792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837792 prefixEnd_837792 := by exact prefixLift 837792
  have htrace : WordTrace (prefixWord ++ tailWord_837792) baseStart_837792 baseEnd_837792 := by
    simpa [prefixWord, tailWord_837792, baseEnd_837792] using wordTrace_append hprefix tailTrace_837792
  have hstable : (prefixWord ++ tailWord_837792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837792).length < 2 ^ (prefixWord ++ tailWord_837792).sum := by decide
  have hdescent : baseEnd_837792 < baseStart_837792 := by decide
  rcases family_descends (prefixWord ++ tailWord_837792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837805 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_837805 : Nat := 118140960795 + 837805 * 2 ^ 59
def prefixEnd_837805 : Nat := 4983230072969 + 3 ^ 40 * 837805 * 2
def baseEnd_837805 : Nat := 430196659740199817784511

theorem tailTrace_837805 : CollatzResearch.WordTrace tailWord_837805 prefixEnd_837805 430196659740199817784511 := by
  unfold tailWord_837805
  simp only [CollatzResearch.WordTrace]
  refine ⟨30557258729783045547474869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20371505819855363698316579 30557258729783045547474869)
  ·
    refine ⟨2864743005917160520075769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30557258729783045547474869 2864743005917160520075769)
    ·
      refine ⟨2148557254437870390056827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2864743005917160520075769 2148557254437870390056827)
      ·
        refine ⟨3222835881656805585085241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2148557254437870390056827 3222835881656805585085241)
        ·
          refine ⟨2417126911242604188813931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3222835881656805585085241 2417126911242604188813931)
          ·
            refine ⟨3625690366863906283220897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417126911242604188813931 3625690366863906283220897)
            ·
              refine ⟨2719267775147929712415673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3625690366863906283220897 2719267775147929712415673)
              ·
                refine ⟨2039450831360947284311755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2719267775147929712415673 2039450831360947284311755)
                ·
                  refine ⟨3059176247041420926467633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039450831360947284311755 3059176247041420926467633)
                  ·
                    refine ⟨2294382185281065694850725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3059176247041420926467633 2294382185281065694850725)
                    ·
                      refine ⟨430196659740199817784511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2294382185281065694850725 430196659740199817784511)
                      ·
                        rfl

theorem cell23_837805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_837805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837805 prefixEnd_837805 := by exact prefixLift 837805
  have htrace : WordTrace (prefixWord ++ tailWord_837805) baseStart_837805 baseEnd_837805 := by
    simpa [prefixWord, tailWord_837805, baseEnd_837805] using wordTrace_append hprefix tailTrace_837805
  have hstable : (prefixWord ++ tailWord_837805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837805).length < 2 ^ (prefixWord ++ tailWord_837805).sum := by decide
  have hdescent : baseEnd_837805 < baseStart_837805 := by decide
  rcases family_descends (prefixWord ++ tailWord_837805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837806 : List Nat := [4, 1, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_837806 : Nat := 118140960795 + 837806 * 2 ^ 59
def prefixEnd_837806 : Nat := 4983230072969 + 3 ^ 40 * 837806 * 2
def baseEnd_837806 : Nat := 143399057740284771290669

theorem tailTrace_837806 : CollatzResearch.WordTrace tailWord_837806 prefixEnd_837806 143399057740284771290669 := by
  unfold tailWord_837806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3819661900347427839782659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20371530135186281812174181 3819661900347427839782659)
  ·
    refine ⟨5729492850521141759673989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3819661900347427839782659 5729492850521141759673989)
    ·
      refine ⟨1074279909472714079938873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5729492850521141759673989 1074279909472714079938873)
      ·
        refine ⟨805709932104535559954155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1074279909472714079938873 805709932104535559954155)
        ·
          refine ⟨1208564898156803339931233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805709932104535559954155 1208564898156803339931233)
          ·
            refine ⟨906423673617602504948425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208564898156803339931233 906423673617602504948425)
            ·
              refine ⟨679817755213201878711319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906423673617602504948425 679817755213201878711319)
              ·
                refine ⟨1019726632819802818066979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679817755213201878711319 1019726632819802818066979)
                ·
                  refine ⟨1529589949229704227100469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019726632819802818066979 1529589949229704227100469)
                  ·
                    refine ⟨143399057740284771290669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1529589949229704227100469 143399057740284771290669)
                    ·
                      rfl

theorem cell23_837806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_837806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837806 prefixEnd_837806 := by exact prefixLift 837806
  have htrace : WordTrace (prefixWord ++ tailWord_837806) baseStart_837806 baseEnd_837806 := by
    simpa [prefixWord, tailWord_837806, baseEnd_837806] using wordTrace_append hprefix tailTrace_837806
  have hstable : (prefixWord ++ tailWord_837806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837806).length < 2 ^ (prefixWord ++ tailWord_837806).sum := by decide
  have hdescent : baseEnd_837806 < baseStart_837806 := by decide
  rcases family_descends (prefixWord ++ tailWord_837806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837809 : List Nat := [1, 2, 2, 5, 2, 2, 2, 1, 1, 1, 4]
def baseStart_837809 : Nat := 118140960795 + 837809 * 2 ^ 59
def prefixEnd_837809 : Nat := 4983230072969 + 3 ^ 40 * 837809 * 2
def baseEnd_837809 : Nat := 430198713662817802134493

theorem tailTrace_837809 : CollatzResearch.WordTrace tailWord_837809 prefixEnd_837809 430198713662817802134493 := by
  unfold tailWord_837809
  simp only [CollatzResearch.WordTrace]
  refine ⟨30557404621768554230620481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20371603081179036153746987 30557404621768554230620481)
  ·
    refine ⟨22918053466326415672965361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30557404621768554230620481 22918053466326415672965361)
    ·
      refine ⟨17188540099744811754724021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22918053466326415672965361 17188540099744811754724021)
      ·
        refine ⟨1611425634351076102005377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17188540099744811754724021 1611425634351076102005377)
        ·
          refine ⟨1208569225763307076504033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1611425634351076102005377 1208569225763307076504033)
          ·
            refine ⟨906426919322480307378025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208569225763307076504033 906426919322480307378025)
            ·
              refine ⟨679820189491860230533519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906426919322480307378025 679820189491860230533519)
              ·
                refine ⟨1019730284237790345800279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679820189491860230533519 1019730284237790345800279)
                ·
                  refine ⟨1529595426356685518700419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019730284237790345800279 1529595426356685518700419)
                  ·
                    refine ⟨2294393139535028278050629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1529595426356685518700419 2294393139535028278050629)
                    ·
                      refine ⟨430198713662817802134493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2294393139535028278050629 430198713662817802134493)
                      ·
                        rfl

theorem cell23_837809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_837809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837809 prefixEnd_837809 := by exact prefixLift 837809
  have htrace : WordTrace (prefixWord ++ tailWord_837809) baseStart_837809 baseEnd_837809 := by
    simpa [prefixWord, tailWord_837809, baseEnd_837809] using wordTrace_append hprefix tailTrace_837809
  have hstable : (prefixWord ++ tailWord_837809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837809).length < 2 ^ (prefixWord ++ tailWord_837809).sum := by decide
  have hdescent : baseEnd_837809 < baseStart_837809 := by decide
  rcases family_descends (prefixWord ++ tailWord_837809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837826 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_837826 : Nat := 118140960795 + 837826 * 2 ^ 59
def prefixEnd_837826 : Nat := 4983230072969 + 3 ^ 40 * 837826 * 2
def baseEnd_837826 : Nat := 430207442833944235621915

theorem tailTrace_837826 : CollatzResearch.WordTrace tailWord_837826 prefixEnd_837826 430207442833944235621915 := by
  unfold tailWord_837826
  simp only [CollatzResearch.WordTrace]
  refine ⟨7639506165676741533497333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20372016441804644089326221 7639506165676741533497333)
  ·
    refine ⟨716203703032194518765375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7639506165676741533497333 716203703032194518765375)
    ·
      refine ⟨1074305554548291778148063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 716203703032194518765375 1074305554548291778148063)
      ·
        refine ⟨1611458331822437667222095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074305554548291778148063 1611458331822437667222095)
        ·
          refine ⟨2417187497733656500833143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611458331822437667222095 2417187497733656500833143)
          ·
            refine ⟨3625781246600484751249715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417187497733656500833143 3625781246600484751249715)
            ·
              refine ⟨5438671869900727126874573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3625781246600484751249715 5438671869900727126874573)
              ·
                refine ⟨2039501951212772672577965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5438671869900727126874573 2039501951212772672577965)
                ·
                  refine ⟨764813231704789752216737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2039501951212772672577965 764813231704789752216737)
                  ·
                    refine ⟨573609923778592314162553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 764813231704789752216737 573609923778592314162553)
                    ·
                      refine ⟨430207442833944235621915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573609923778592314162553 430207442833944235621915)
                      ·
                        rfl

theorem cell23_837826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_837826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837826 prefixEnd_837826 := by exact prefixLift 837826
  have htrace : WordTrace (prefixWord ++ tailWord_837826) baseStart_837826 baseEnd_837826 := by
    simpa [prefixWord, tailWord_837826, baseEnd_837826] using wordTrace_append hprefix tailTrace_837826
  have hstable : (prefixWord ++ tailWord_837826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837826).length < 2 ^ (prefixWord ++ tailWord_837826).sum := by decide
  have hdescent : baseEnd_837826 < baseStart_837826 := by decide
  rcases family_descends (prefixWord ++ tailWord_837826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837842 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_837842 : Nat := 118140960795 + 837842 * 2 ^ 59
def prefixEnd_837842 : Nat := 4983230072969 + 3 ^ 40 * 837842 * 2
def baseEnd_837842 : Nat := 430215658524416173021841

theorem tailTrace_837842 : CollatzResearch.WordTrace tailWord_837842 prefixEnd_837842 430215658524416173021841 := by
  unfold tailWord_837842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7639652057662250216642945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20372405487099333911047853 7639652057662250216642945)
  ·
    refine ⟨5729739043246687662482209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7639652057662250216642945 5729739043246687662482209)
    ·
      refine ⟨4297304282435015746861657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5729739043246687662482209 4297304282435015746861657)
      ·
        refine ⟨3222978211826261810146243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4297304282435015746861657 3222978211826261810146243)
        ·
          refine ⟨4834467317739392715219365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3222978211826261810146243 4834467317739392715219365)
          ·
            refine ⟨906462622076136134103631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4834467317739392715219365 906462622076136134103631)
            ·
              refine ⟨1359693933114204201155447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906462622076136134103631 1359693933114204201155447)
              ·
                refine ⟨2039540899671306301733171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359693933114204201155447 2039540899671306301733171)
                ·
                  refine ⟨3059311349506959452599757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039540899671306301733171 3059311349506959452599757)
                  ·
                    refine ⟨1147241756065109794724909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3059311349506959452599757 1147241756065109794724909)
                    ·
                      refine ⟨430215658524416173021841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1147241756065109794724909 430215658524416173021841)
                      ·
                        rfl

theorem cell23_837842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_837842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837842 prefixEnd_837842 := by exact prefixLift 837842
  have htrace : WordTrace (prefixWord ++ tailWord_837842) baseStart_837842 baseEnd_837842 := by
    simpa [prefixWord, tailWord_837842, baseEnd_837842] using wordTrace_append hprefix tailTrace_837842
  have hstable : (prefixWord ++ tailWord_837842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837842).length < 2 ^ (prefixWord ++ tailWord_837842).sum := by decide
  have hdescent : baseEnd_837842 < baseStart_837842 := by decide
  rcases family_descends (prefixWord ++ tailWord_837842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837868 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_837868 : Nat := 118140960795 + 837868 * 2 ^ 59
def prefixEnd_837868 : Nat := 4983230072969 + 3 ^ 40 * 837868 * 2
def baseEnd_837868 : Nat := 430229009021433071296721

theorem tailTrace_837868 : CollatzResearch.WordTrace tailWord_837868 prefixEnd_837868 430229009021433071296721 := by
  unfold tailWord_837868
  simp only [CollatzResearch.WordTrace]
  refine ⟨15279778264277403653509129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20373037685703204871345505 15279778264277403653509129)
  ·
    refine ⟨11459833698208052740131847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15279778264277403653509129 11459833698208052740131847)
    ·
      refine ⟨17189750547312079110197771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11459833698208052740131847 17189750547312079110197771)
      ·
        refine ⟨25784625820968118665296657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17189750547312079110197771 25784625820968118665296657)
        ·
          refine ⟨19338469365726088998972493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25784625820968118665296657 19338469365726088998972493)
          ·
            refine ⟨7251926012147283374614685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19338469365726088998972493 7251926012147283374614685)
            ·
              refine ⟨2719472254555231265480507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7251926012147283374614685 2719472254555231265480507)
              ·
                refine ⟨4079208381832846898220761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719472254555231265480507 4079208381832846898220761)
                ·
                  refine ⟨3059406286374635173665571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4079208381832846898220761 3059406286374635173665571)
                  ·
                    refine ⟨4589109429561952760498357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3059406286374635173665571 4589109429561952760498357)
                    ·
                      refine ⟨430229009021433071296721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4589109429561952760498357 430229009021433071296721)
                      ·
                        rfl

theorem cell23_837868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_837868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837868 prefixEnd_837868 := by exact prefixLift 837868
  have htrace : WordTrace (prefixWord ++ tailWord_837868) baseStart_837868 baseEnd_837868 := by
    simpa [prefixWord, tailWord_837868, baseEnd_837868] using wordTrace_append hprefix tailTrace_837868
  have hstable : (prefixWord ++ tailWord_837868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837868).length < 2 ^ (prefixWord ++ tailWord_837868).sum := by decide
  have hdescent : baseEnd_837868 < baseStart_837868 := by decide
  rcases family_descends (prefixWord ++ tailWord_837868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837882 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2]
def baseStart_837882 : Nat := 118140960795 + 837882 * 2 ^ 59
def prefixEnd_837882 : Nat := 4983230072969 + 3 ^ 40 * 837882 * 2
def baseEnd_837882 : Nat := 430236197750596016521657

theorem tailTrace_837882 : CollatzResearch.WordTrace tailWord_837882 prefixEnd_837882 430236197750596016521657 := by
  unfold tailWord_837882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7640016787626021924506975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20373378100336058465351933 7640016787626021924506975)
  ·
    refine ⟨11460025181439032886760463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7640016787626021924506975 11460025181439032886760463)
    ·
      refine ⟨17190037772158549330140695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11460025181439032886760463 17190037772158549330140695)
      ·
        refine ⟨25785056658237823995211043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17190037772158549330140695 25785056658237823995211043)
        ·
          refine ⟨38677584987356735992816565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25785056658237823995211043 38677584987356735992816565)
          ·
            refine ⟨3626023592564693999326553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38677584987356735992816565 3626023592564693999326553)
            ·
              refine ⟨2719517694423520499494915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3626023592564693999326553 2719517694423520499494915)
              ·
                refine ⟨4079276541635280749242373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719517694423520499494915 4079276541635280749242373)
                ·
                  refine ⟨764864351556615140482945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4079276541635280749242373 764864351556615140482945)
                  ·
                    refine ⟨573648263667461355362209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 764864351556615140482945 573648263667461355362209)
                    ·
                      refine ⟨430236197750596016521657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573648263667461355362209 430236197750596016521657)
                      ·
                        rfl

theorem cell23_837882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2].length) (baseStart_837882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837882 prefixEnd_837882 := by exact prefixLift 837882
  have htrace : WordTrace (prefixWord ++ tailWord_837882) baseStart_837882 baseEnd_837882 := by
    simpa [prefixWord, tailWord_837882, baseEnd_837882] using wordTrace_append hprefix tailTrace_837882
  have hstable : (prefixWord ++ tailWord_837882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837882).length < 2 ^ (prefixWord ++ tailWord_837882).sum := by decide
  have hdescent : baseEnd_837882 < baseStart_837882 := by decide
  rcases family_descends (prefixWord ++ tailWord_837882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837888 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 7]
def baseStart_837888 : Nat := 118140960795 + 837888 * 2 ^ 59
def prefixEnd_837888 : Nat := 4983230072969 + 3 ^ 40 * 837888 * 2
def baseEnd_837888 : Nat := 47804364292724777005181

theorem tailTrace_837888 : CollatzResearch.WordTrace tailWord_837888 prefixEnd_837888 47804364292724777005181 := by
  unfold tailWord_837888
  simp only [CollatzResearch.WordTrace]
  refine ⟨15280142994241175361373159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20373523992321567148497545 15280142994241175361373159)
  ·
    refine ⟨22920214491361763042059739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15280142994241175361373159 22920214491361763042059739)
    ·
      refine ⟨34380321737042644563089609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22920214491361763042059739 34380321737042644563089609)
      ·
        refine ⟨25785241302781983422317207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34380321737042644563089609 25785241302781983422317207)
        ·
          refine ⟨38677861954172975133475811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25785241302781983422317207 38677861954172975133475811)
          ·
            refine ⟨58016792931259462700213717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38677861954172975133475811 58016792931259462700213717)
            ·
              refine ⟨1359768584326393657036259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58016792931259462700213717 1359768584326393657036259)
              ·
                refine ⟨2039652876489590485554389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359768584326393657036259 2039652876489590485554389)
                ·
                  refine ⟨47804364292724777005181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2039652876489590485554389 47804364292724777005181)
                  ·
                    rfl

theorem cell23_837888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 7].length) (baseStart_837888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837888 prefixEnd_837888 := by exact prefixLift 837888
  have htrace : WordTrace (prefixWord ++ tailWord_837888) baseStart_837888 baseEnd_837888 := by
    simpa [prefixWord, tailWord_837888, baseEnd_837888] using wordTrace_append hprefix tailTrace_837888
  have hstable : (prefixWord ++ tailWord_837888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837888).length < 2 ^ (prefixWord ++ tailWord_837888).sum := by decide
  have hdescent : baseEnd_837888 < baseStart_837888 := by decide
  rcases family_descends (prefixWord ++ tailWord_837888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837933 : List Nat := [1, 5, 3, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_837933 : Nat := 118140960795 + 837933 * 2 ^ 59
def prefixEnd_837933 : Nat := 4983230072969 + 3 ^ 40 * 837933 * 2
def baseEnd_837933 : Nat := 430262385263975316983923

theorem tailTrace_837933 : CollatzResearch.WordTrace tailWord_837933 prefixEnd_837933 430262385263975316983923 := by
  unfold tailWord_837933
  simp only [CollatzResearch.WordTrace]
  refine ⟨30561927273319323408134453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20374618182212882272089635 30561927273319323408134453)
  ·
    refine ⟨2865180681873686569512605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30561927273319323408134453 2865180681873686569512605)
    ·
      refine ⟨1074442755702632463567227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2865180681873686569512605 1074442755702632463567227)
      ·
        refine ⟨1611664133553948695350841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074442755702632463567227 1611664133553948695350841)
        ·
          refine ⟨1208748100165461521513131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1611664133553948695350841 1208748100165461521513131)
          ·
            refine ⟨1813122150248192282269697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208748100165461521513131 1813122150248192282269697)
            ·
              refine ⟨1359841612686144211702273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1813122150248192282269697 1359841612686144211702273)
              ·
                refine ⟨1019881209514608158776705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359841612686144211702273 1019881209514608158776705)
                ·
                  refine ⟨764910907135956119082529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1019881209514608158776705 764910907135956119082529)
                  ·
                    refine ⟨573683180351967089311897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 764910907135956119082529 573683180351967089311897)
                    ·
                      refine ⟨430262385263975316983923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573683180351967089311897 430262385263975316983923)
                      ·
                        rfl

theorem cell23_837933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_837933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837933 prefixEnd_837933 := by exact prefixLift 837933
  have htrace : WordTrace (prefixWord ++ tailWord_837933) baseStart_837933 baseEnd_837933 := by
    simpa [prefixWord, tailWord_837933, baseEnd_837933] using wordTrace_append hprefix tailTrace_837933
  have hstable : (prefixWord ++ tailWord_837933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837933).length < 2 ^ (prefixWord ++ tailWord_837933).sum := by decide
  have hdescent : baseEnd_837933 < baseStart_837933 := by decide
  rcases family_descends (prefixWord ++ tailWord_837933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837945 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 5]
def baseStart_837945 : Nat := 118140960795 + 837945 * 2 ^ 59
def prefixEnd_837945 : Nat := 4983230072969 + 3 ^ 40 * 837945 * 2
def baseEnd_837945 : Nat := 430268547031829270033867

theorem tailTrace_837945 : CollatzResearch.WordTrace tailWord_837945 prefixEnd_837945 430268547031829270033867 := by
  unfold tailWord_837945
  simp only [CollatzResearch.WordTrace]
  refine ⟨30562364949275849457571289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20374909966183899638380859 30562364949275849457571289)
  ·
    refine ⟨22921773711956887093178467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30562364949275849457571289 22921773711956887093178467)
    ·
      refine ⟨34382660567935330639767701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22921773711956887093178467 34382660567935330639767701)
      ·
        refine ⟨1611687214121968623739111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34382660567935330639767701 1611687214121968623739111)
        ·
          refine ⟨2417530821182952935608667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611687214121968623739111 2417530821182952935608667)
          ·
            refine ⟨3626296231774429403413001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417530821182952935608667 3626296231774429403413001)
            ·
              refine ⟨2719722173830822052559751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3626296231774429403413001 2719722173830822052559751)
              ·
                refine ⟨4079583260746233078839627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719722173830822052559751 4079583260746233078839627)
                ·
                  refine ⟨6119374891119349618259441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4079583260746233078839627 6119374891119349618259441)
                  ·
                    refine ⟨4589531168339512213694581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6119374891119349618259441 4589531168339512213694581)
                    ·
                      refine ⟨430268547031829270033867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4589531168339512213694581 430268547031829270033867)
                      ·
                        rfl

theorem cell23_837945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_837945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837945 prefixEnd_837945 := by exact prefixLift 837945
  have htrace : WordTrace (prefixWord ++ tailWord_837945) baseStart_837945 baseEnd_837945 := by
    simpa [prefixWord, tailWord_837945, baseEnd_837945] using wordTrace_append hprefix tailTrace_837945
  have hstable : (prefixWord ++ tailWord_837945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837945).length < 2 ^ (prefixWord ++ tailWord_837945).sum := by decide
  have hdescent : baseEnd_837945 < baseStart_837945 := by decide
  rcases family_descends (prefixWord ++ tailWord_837945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837955 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 1, 6, 2]
def baseStart_837955 : Nat := 118140960795 + 837955 * 2 ^ 59
def prefixEnd_837955 : Nat := 4983230072969 + 3 ^ 40 * 837955 * 2
def baseEnd_837955 : Nat := 430273681838374230908821

theorem tailTrace_837955 : CollatzResearch.WordTrace tailWord_837955 prefixEnd_837955 430273681838374230908821 := by
  unfold tailWord_837955
  simp only [CollatzResearch.WordTrace]
  refine ⟨30562729679239621165435319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20375153119493080776956879 30562729679239621165435319)
  ·
    refine ⟨45844094518859431748152979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30562729679239621165435319 45844094518859431748152979)
    ·
      refine ⟨68766141778289147622229469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45844094518859431748152979 68766141778289147622229469)
      ·
        refine ⟨25787303166858430358336051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68766141778289147622229469 25787303166858430358336051)
        ·
          refine ⟨38680954750287645537504077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25787303166858430358336051 38680954750287645537504077)
          ·
            refine ⟨14505358031357867076564029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38680954750287645537504077 14505358031357867076564029)
            ·
              refine ⟨5439509261759200153711511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14505358031357867076564029 5439509261759200153711511)
              ·
                refine ⟨8159263892638800230567267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5439509261759200153711511 8159263892638800230567267)
                ·
                  refine ⟨12238895838958200345850901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8159263892638800230567267 12238895838958200345850901)
                  ·
                    refine ⟨573698242451165641211761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12238895838958200345850901 573698242451165641211761)
                    ·
                      refine ⟨430273681838374230908821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573698242451165641211761 430273681838374230908821)
                      ·
                        rfl

theorem cell23_837955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 6, 2].length) (baseStart_837955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837955 prefixEnd_837955 := by exact prefixLift 837955
  have htrace : WordTrace (prefixWord ++ tailWord_837955) baseStart_837955 baseEnd_837955 := by
    simpa [prefixWord, tailWord_837955, baseEnd_837955] using wordTrace_append hprefix tailTrace_837955
  have hstable : (prefixWord ++ tailWord_837955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837955).length < 2 ^ (prefixWord ++ tailWord_837955).sum := by decide
  have hdescent : baseEnd_837955 < baseStart_837955 := by decide
  rcases family_descends (prefixWord ++ tailWord_837955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837972 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_837972 : Nat := 118140960795 + 837972 * 2 ^ 59
def prefixEnd_837972 : Nat := 4983230072969 + 3 ^ 40 * 837972 * 2
def baseEnd_837972 : Nat := 430282411009500664396243

theorem tailTrace_837972 : CollatzResearch.WordTrace tailWord_837972 prefixEnd_837972 430282411009500664396243 := by
  unfold tailWord_837972
  simp only [CollatzResearch.WordTrace]
  refine ⟨15281674860089016534402085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20375566480118688712536113 15281674860089016534402085)
  ·
    refine ⟨2865314036266690600200391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15281674860089016534402085 2865314036266690600200391)
    ·
      refine ⟨4297971054400035900300587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2865314036266690600200391 4297971054400035900300587)
      ·
        refine ⟨6446956581600053850450881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4297971054400035900300587 6446956581600053850450881)
        ·
          refine ⟨4835217436200040387838161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6446956581600053850450881 4835217436200040387838161)
          ·
            refine ⟨3626413077150030290878621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4835217436200040387838161 3626413077150030290878621)
            ·
              refine ⟨1359904903931261359079483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3626413077150030290878621 1359904903931261359079483)
              ·
                refine ⟨2039857355896892038619225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359904903931261359079483 2039857355896892038619225)
                ·
                  refine ⟨1529893016922669028964419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2039857355896892038619225 1529893016922669028964419)
                  ·
                    refine ⟨2294839525384003543446629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1529893016922669028964419 2294839525384003543446629)
                    ·
                      refine ⟨430282411009500664396243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2294839525384003543446629 430282411009500664396243)
                      ·
                        rfl

theorem cell23_837972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_837972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837972 prefixEnd_837972 := by exact prefixLift 837972
  have htrace : WordTrace (prefixWord ++ tailWord_837972) baseStart_837972 baseEnd_837972 := by
    simpa [prefixWord, tailWord_837972, baseEnd_837972] using wordTrace_append hprefix tailTrace_837972
  have hstable : (prefixWord ++ tailWord_837972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837972).length < 2 ^ (prefixWord ++ tailWord_837972).sum := by decide
  have hdescent : baseEnd_837972 < baseStart_837972 := by decide
  rcases family_descends (prefixWord ++ tailWord_837972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837975 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 3]
def baseStart_837975 : Nat := 118140960795 + 837975 * 2 ^ 59
def prefixEnd_837975 : Nat := 4983230072969 + 3 ^ 40 * 837975 * 2
def baseEnd_837975 : Nat := 430283951451464152658729

theorem tailTrace_837975 : CollatzResearch.WordTrace tailWord_837975 prefixEnd_837975 430283951451464152658729 := by
  unfold tailWord_837975
  simp only [CollatzResearch.WordTrace]
  refine ⟨30563459139167164581163379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20375639426111443054108919 30563459139167164581163379)
  ·
    refine ⟨45845188708750746871745069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30563459139167164581163379 45845188708750746871745069)
    ·
      refine ⟨17191945765781530076904401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45845188708750746871745069 17191945765781530076904401)
      ·
        refine ⟨12893959324336147557678301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17191945765781530076904401 12893959324336147557678301)
        ·
          refine ⟨4835234746626055334129363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12893959324336147557678301 4835234746626055334129363)
          ·
            refine ⟨7252852119939083001194045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4835234746626055334129363 7252852119939083001194045)
            ·
              refine ⟨2719819544977156125447767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7252852119939083001194045 2719819544977156125447767)
              ·
                refine ⟨4079729317465734188171651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719819544977156125447767 4079729317465734188171651)
                ·
                  refine ⟨6119593976198601282257477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4079729317465734188171651 6119593976198601282257477)
                  ·
                    refine ⟨1147423870537237740423277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6119593976198601282257477 1147423870537237740423277)
                    ·
                      refine ⟨430283951451464152658729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1147423870537237740423277 430283951451464152658729)
                      ·
                        rfl

theorem cell23_837975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_837975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837975 prefixEnd_837975 := by exact prefixLift 837975
  have htrace : WordTrace (prefixWord ++ tailWord_837975) baseStart_837975 baseEnd_837975 := by
    simpa [prefixWord, tailWord_837975, baseEnd_837975] using wordTrace_append hprefix tailTrace_837975
  have hstable : (prefixWord ++ tailWord_837975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837975).length < 2 ^ (prefixWord ++ tailWord_837975).sum := by decide
  have hdescent : baseEnd_837975 < baseStart_837975 := by decide
  rcases family_descends (prefixWord ++ tailWord_837975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_837978 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 8]
def baseStart_837978 : Nat := 118140960795 + 837978 * 2 ^ 59
def prefixEnd_837978 : Nat := 4983230072969 + 3 ^ 40 * 837978 * 2
def baseEnd_837978 : Nat := 47809499099269737880135

theorem tailTrace_837978 : CollatzResearch.WordTrace tailWord_837978 prefixEnd_837978 47809499099269737880135 := by
  unfold tailWord_837978
  simp only [CollatzResearch.WordTrace]
  refine ⟨7640892139539074023380647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20375712372104197395681725 7640892139539074023380647)
  ·
    refine ⟨11461338209308611035070971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7640892139539074023380647 11461338209308611035070971)
    ·
      refine ⟨17192007313962916552606457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11461338209308611035070971 17192007313962916552606457)
      ·
        refine ⟨12894005485472187414454843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17192007313962916552606457 12894005485472187414454843)
        ·
          refine ⟨19341008228208281121682265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12894005485472187414454843 19341008228208281121682265)
          ·
            refine ⟨14505756171156210841261699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19341008228208281121682265 14505756171156210841261699)
            ·
              refine ⟨21758634256734316261892549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14505756171156210841261699 21758634256734316261892549)
              ·
                refine ⟨4079743923137684299104853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21758634256734316261892549 4079743923137684299104853)
                ·
                  refine ⟨47809499099269737880135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4079743923137684299104853 47809499099269737880135)
                  ·
                    rfl

theorem cell23_837978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_837978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_837978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_837978 prefixEnd_837978 := by exact prefixLift 837978
  have htrace : WordTrace (prefixWord ++ tailWord_837978) baseStart_837978 baseEnd_837978 := by
    simpa [prefixWord, tailWord_837978, baseEnd_837978] using wordTrace_append hprefix tailTrace_837978
  have hstable : (prefixWord ++ tailWord_837978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_837978).length < 2 ^ (prefixWord ++ tailWord_837978).sum := by decide
  have hdescent : baseEnd_837978 < baseStart_837978 := by decide
  rcases family_descends (prefixWord ++ tailWord_837978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838042 : List Nat := [3, 1, 1, 4, 1, 2, 2, 3, 1, 5]
def baseStart_838042 : Nat := 118140960795 + 838042 * 2 ^ 59
def prefixEnd_838042 : Nat := 4983230072969 + 3 ^ 40 * 838042 * 2
def baseEnd_838042 : Nat := 143439451551771796840307

theorem tailTrace_838042 : CollatzResearch.WordTrace tailWord_838042 prefixEnd_838042 143439451551771796840307 := by
  unfold tailWord_838042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7641475707481108755963095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20377268553282956682568253 7641475707481108755963095)
  ·
    refine ⟨11462213561221663133944643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7641475707481108755963095 11462213561221663133944643)
    ·
      refine ⟨17193320341832494700916965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11462213561221663133944643 17193320341832494700916965)
      ·
        refine ⟨3223747564093592756421931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17193320341832494700916965 3223747564093592756421931)
        ·
          refine ⟨4835621346140389134632897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3223747564093592756421931 4835621346140389134632897)
          ·
            refine ⟨3626716009605291850974673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4835621346140389134632897 3626716009605291850974673)
            ·
              refine ⟨2720037007203968888231005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3626716009605291850974673 2720037007203968888231005)
              ·
                refine ⟨1020013877701488333086627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2720037007203968888231005 1020013877701488333086627)
                ·
                  refine ⟨1530020816552232499629941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020013877701488333086627 1530020816552232499629941)
                  ·
                    refine ⟨143439451551771796840307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1530020816552232499629941 143439451551771796840307)
                    ·
                      rfl

theorem cell23_838042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_838042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838042 prefixEnd_838042 := by exact prefixLift 838042
  have htrace : WordTrace (prefixWord ++ tailWord_838042) baseStart_838042 baseEnd_838042 := by
    simpa [prefixWord, tailWord_838042, baseEnd_838042] using wordTrace_append hprefix tailTrace_838042
  have hstable : (prefixWord ++ tailWord_838042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838042).length < 2 ^ (prefixWord ++ tailWord_838042).sum := by decide
  have hdescent : baseEnd_838042 < baseStart_838042 := by decide
  rcases family_descends (prefixWord ++ tailWord_838042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838056 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_838056 : Nat := 118140960795 + 838056 * 2 ^ 59
def prefixEnd_838056 : Nat := 4983230072969 + 3 ^ 40 * 838056 * 2
def baseEnd_838056 : Nat := 430325543384478335745857

theorem tailTrace_838056 : CollatzResearch.WordTrace tailWord_838056 prefixEnd_838056 430325543384478335745857 := by
  unfold tailWord_838056
  simp only [CollatzResearch.WordTrace]
  refine ⟨15283206725936857707431011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20377608967915810276574681 15283206725936857707431011)
  ·
    refine ⟨22924810088905286561146517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15283206725936857707431011 22924810088905286561146517)
    ·
      refine ⟨1074600472917435307553743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22924810088905286561146517 1074600472917435307553743)
      ·
        refine ⟨1611900709376152961330615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074600472917435307553743 1611900709376152961330615)
        ·
          refine ⟨2417851064064229441995923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611900709376152961330615 2417851064064229441995923)
          ·
            refine ⟨3626776596096344162993885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417851064064229441995923 3626776596096344162993885)
            ·
              refine ⟨1360041223536129061122707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3626776596096344162993885 1360041223536129061122707)
              ·
                refine ⟨2040061835304193591684061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360041223536129061122707 2040061835304193591684061)
                ·
                  refine ⟨765023188239072596881523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2040061835304193591684061 765023188239072596881523)
                  ·
                    refine ⟨1147534782358608895322285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 765023188239072596881523 1147534782358608895322285)
                    ·
                      refine ⟨430325543384478335745857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1147534782358608895322285 430325543384478335745857)
                      ·
                        rfl

theorem cell23_838056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_838056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838056 prefixEnd_838056 := by exact prefixLift 838056
  have htrace : WordTrace (prefixWord ++ tailWord_838056) baseStart_838056 baseEnd_838056 := by
    simpa [prefixWord, tailWord_838056, baseEnd_838056] using wordTrace_append hprefix tailTrace_838056
  have hstable : (prefixWord ++ tailWord_838056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838056).length < 2 ^ (prefixWord ++ tailWord_838056).sum := by decide
  have hdescent : baseEnd_838056 < baseStart_838056 := by decide
  rcases family_descends (prefixWord ++ tailWord_838056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838129 : List Nat := [1, 2, 2, 2, 3, 1, 1, 5, 2, 1, 3]
def baseStart_838129 : Nat := 118140960795 + 838129 * 2 ^ 59
def prefixEnd_838129 : Nat := 4983230072969 + 3 ^ 40 * 838129 * 2
def baseEnd_838129 : Nat := 430363027472256550133021

theorem tailTrace_838129 : CollatzResearch.WordTrace tailWord_838129 prefixEnd_838129 430363027472256550133021 := by
  unfold tailWord_838129
  simp only [CollatzResearch.WordTrace]
  refine ⟨30569075980609248882269441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20379383987072832588179627 30569075980609248882269441)
  ·
    refine ⟨22926806985456936661702081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30569075980609248882269441 22926806985456936661702081)
    ·
      refine ⟨17195105239092702496276561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22926806985456936661702081 17195105239092702496276561)
      ·
        refine ⟨12896328929319526872207421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17195105239092702496276561 12896328929319526872207421)
        ·
          refine ⟨4836123348494822577077783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12896328929319526872207421 4836123348494822577077783)
          ·
            refine ⟨7254185022742233865616675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836123348494822577077783 7254185022742233865616675)
            ·
              refine ⟨10881277534113350798425013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7254185022742233865616675 10881277534113350798425013)
              ·
                refine ⟨1020119768823126637352345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10881277534113350798425013 1020119768823126637352345)
                ·
                  refine ⟨765089826617344978014259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1020119768823126637352345 765089826617344978014259)
                  ·
                    refine ⟨1147634739926017467021389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 765089826617344978014259 1147634739926017467021389)
                    ·
                      refine ⟨430363027472256550133021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1147634739926017467021389 430363027472256550133021)
                      ·
                        rfl

theorem cell23_838129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_838129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838129 prefixEnd_838129 := by exact prefixLift 838129
  have htrace : WordTrace (prefixWord ++ tailWord_838129) baseStart_838129 baseEnd_838129 := by
    simpa [prefixWord, tailWord_838129, baseEnd_838129] using wordTrace_append hprefix tailTrace_838129
  have hstable : (prefixWord ++ tailWord_838129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838129).length < 2 ^ (prefixWord ++ tailWord_838129).sum := by decide
  have hdescent : baseEnd_838129 < baseStart_838129 := by decide
  rcases family_descends (prefixWord ++ tailWord_838129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838150 : List Nat := [6, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_838150 : Nat := 118140960795 + 838150 * 2 ^ 59
def prefixEnd_838150 : Nat := 4983230072969 + 3 ^ 40 * 838150 * 2
def baseEnd_838150 : Nat := 430373810566000967970425

theorem tailTrace_838150 : CollatzResearch.WordTrace tailWord_838150 prefixEnd_838150 430373810566000967970425 := by
  unfold tailWord_838150
  simp only [CollatzResearch.WordTrace]
  refine ⟨955307559797911545899497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20379894609022112979189269 955307559797911545899497)
  ·
    refine ⟨716480669848433659424623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 955307559797911545899497 716480669848433659424623)
    ·
      refine ⟨1074721004772650489136935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 716480669848433659424623 1074721004772650489136935)
      ·
        refine ⟨1612081507158975733705403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074721004772650489136935 1612081507158975733705403)
        ·
          refine ⟨2418122260738463600558105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612081507158975733705403 2418122260738463600558105)
          ·
            refine ⟨1813591695553847700418579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2418122260738463600558105 1813591695553847700418579)
            ·
              refine ⟨2720387543330771550627869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813591695553847700418579 2720387543330771550627869)
              ·
                refine ⟨1020145328749039331485451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2720387543330771550627869 1020145328749039331485451)
                ·
                  refine ⟨1530217993123558997228177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020145328749039331485451 1530217993123558997228177)
                  ·
                    refine ⟨1147663494842669247921133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1530217993123558997228177 1147663494842669247921133)
                    ·
                      refine ⟨430373810566000967970425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1147663494842669247921133 430373810566000967970425)
                      ·
                        rfl

theorem cell23_838150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_838150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838150 prefixEnd_838150 := by exact prefixLift 838150
  have htrace : WordTrace (prefixWord ++ tailWord_838150) baseStart_838150 baseEnd_838150 := by
    simpa [prefixWord, tailWord_838150, baseEnd_838150] using wordTrace_append hprefix tailTrace_838150
  have hstable : (prefixWord ++ tailWord_838150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838150).length < 2 ^ (prefixWord ++ tailWord_838150).sum := by decide
  have hdescent : baseEnd_838150 < baseStart_838150 := by decide
  rcases family_descends (prefixWord ++ tailWord_838150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838156 : List Nat := [2, 2, 1, 2, 4, 2, 1, 3, 1, 3, 2]
def baseStart_838156 : Nat := 118140960795 + 838156 * 2 ^ 59
def prefixEnd_838156 : Nat := 4983230072969 + 3 ^ 40 * 838156 * 2
def baseEnd_838156 : Nat := 430376891449927944495397

theorem tailTrace_838156 : CollatzResearch.WordTrace tailWord_838156 prefixEnd_838156 430376891449927944495397 := by
  unfold tailWord_838156
  simp only [CollatzResearch.WordTrace]
  refine ⟨15285030375755716246751161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20380040501007621662334881 15285030375755716246751161)
  ·
    refine ⟨11463772781816787185063371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15285030375755716246751161 11463772781816787185063371)
    ·
      refine ⟨17195659172725180777595057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11463772781816787185063371 17195659172725180777595057)
      ·
        refine ⟨12896744379543885583196293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17195659172725180777595057 12896744379543885583196293)
        ·
          refine ⟨2418139571164478546849305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12896744379543885583196293 2418139571164478546849305)
          ·
            refine ⟨1813604678373358910136979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2418139571164478546849305 1813604678373358910136979)
            ·
              refine ⟨2720407017560038365205469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813604678373358910136979 2720407017560038365205469)
              ·
                refine ⟨1020152631585014386952051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2720407017560038365205469 1020152631585014386952051)
                ·
                  refine ⟨1530228947377521580428077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020152631585014386952051 1530228947377521580428077)
                  ·
                    refine ⟨573835855266570592660529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1530228947377521580428077 573835855266570592660529)
                    ·
                      refine ⟨430376891449927944495397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573835855266570592660529 430376891449927944495397)
                      ·
                        rfl

theorem cell23_838156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_838156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838156 prefixEnd_838156 := by exact prefixLift 838156
  have htrace : WordTrace (prefixWord ++ tailWord_838156) baseStart_838156 baseEnd_838156 := by
    simpa [prefixWord, tailWord_838156, baseEnd_838156] using wordTrace_append hprefix tailTrace_838156
  have hstable : (prefixWord ++ tailWord_838156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838156).length < 2 ^ (prefixWord ++ tailWord_838156).sum := by decide
  have hdescent : baseEnd_838156 < baseStart_838156 := by decide
  rcases family_descends (prefixWord ++ tailWord_838156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838169 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 4, 2, 2]
def baseStart_838169 : Nat := 118140960795 + 838169 * 2 ^ 59
def prefixEnd_838169 : Nat := 4983230072969 + 3 ^ 40 * 838169 * 2
def baseEnd_838169 : Nat := 430383566698436393632837

theorem tailTrace_838169 : CollatzResearch.WordTrace tailWord_838169 prefixEnd_838169 430383566698436393632837 := by
  unfold tailWord_838169
  simp only [CollatzResearch.WordTrace]
  refine ⟨30570534900464335713725561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20380356600309557142483707 30570534900464335713725561)
  ·
    refine ⟨22927901175348251785294171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30570534900464335713725561 22927901175348251785294171)
    ·
      refine ⟨34391851763022377677941257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22927901175348251785294171 34391851763022377677941257)
      ·
        refine ⟨25793888822266783258455943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34391851763022377677941257 25793888822266783258455943)
        ·
          refine ⟨38690833233400174887683915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25793888822266783258455943 38690833233400174887683915)
          ·
            refine ⟨58036249850100262331525873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38690833233400174887683915 58036249850100262331525873)
            ·
              refine ⟨43527187387575196748644405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58036249850100262331525873 43527187387575196748644405)
              ·
                refine ⟨4080673817585174695185413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43527187387575196748644405 4080673817585174695185413)
                ·
                  refine ⟨765126340797220255347265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4080673817585174695185413 765126340797220255347265)
                  ·
                    refine ⟨573844755597915191510449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 765126340797220255347265 573844755597915191510449)
                    ·
                      refine ⟨430383566698436393632837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573844755597915191510449 430383566698436393632837)
                      ·
                        rfl

theorem cell23_838169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 2, 2].length) (baseStart_838169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838169 prefixEnd_838169 := by exact prefixLift 838169
  have htrace : WordTrace (prefixWord ++ tailWord_838169) baseStart_838169 baseEnd_838169 := by
    simpa [prefixWord, tailWord_838169, baseEnd_838169] using wordTrace_append hprefix tailTrace_838169
  have hstable : (prefixWord ++ tailWord_838169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838169).length < 2 ^ (prefixWord ++ tailWord_838169).sum := by decide
  have hdescent : baseEnd_838169 < baseStart_838169 := by decide
  rcases family_descends (prefixWord ++ tailWord_838169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838180 : List Nat := [2, 3, 1, 5, 1, 1, 3, 1, 2, 1, 3]
def baseStart_838180 : Nat := 118140960795 + 838180 * 2 ^ 59
def prefixEnd_838180 : Nat := 4983230072969 + 3 ^ 40 * 838180 * 2
def baseEnd_838180 : Nat := 430389214985635850595287

theorem tailTrace_838180 : CollatzResearch.WordTrace tailWord_838180 prefixEnd_838180 430389214985635850595287 := by
  unfold tailWord_838180
  simp only [CollatzResearch.WordTrace]
  refine ⟨15285468051712242296187997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20380624068949656394917329 15285468051712242296187997)
  ·
    refine ⟨5732050519392090861070499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15285468051712242296187997 5732050519392090861070499)
    ·
      refine ⟨8598075779088136291605749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5732050519392090861070499 8598075779088136291605749)
      ·
        refine ⟨806069604289512777338039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8598075779088136291605749 806069604289512777338039)
        ·
          refine ⟨1209104406434269166007059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806069604289512777338039 1209104406434269166007059)
          ·
            refine ⟨1813656609651403749010589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209104406434269166007059 1813656609651403749010589)
            ·
              refine ⟨680121228619276405878971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1813656609651403749010589 680121228619276405878971)
              ·
                refine ⟨1020181842928914608818457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680121228619276405878971 1020181842928914608818457)
                ·
                  refine ⟨765136382196685956613843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1020181842928914608818457 765136382196685956613843)
                  ·
                    refine ⟨1147704573295028934920765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 765136382196685956613843 1147704573295028934920765)
                    ·
                      refine ⟨430389214985635850595287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1147704573295028934920765 430389214985635850595287)
                      ·
                        rfl

theorem cell23_838180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_838180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838180 prefixEnd_838180 := by exact prefixLift 838180
  have htrace : WordTrace (prefixWord ++ tailWord_838180) baseStart_838180 baseEnd_838180 := by
    simpa [prefixWord, tailWord_838180, baseEnd_838180] using wordTrace_append hprefix tailTrace_838180
  have hstable : (prefixWord ++ tailWord_838180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838180).length < 2 ^ (prefixWord ++ tailWord_838180).sum := by decide
  have hdescent : baseEnd_838180 < baseStart_838180 := by decide
  rcases family_descends (prefixWord ++ tailWord_838180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838186 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_838186 : Nat := 118140960795 + 838186 * 2 ^ 59
def prefixEnd_838186 : Nat := 4983230072969 + 3 ^ 40 * 838186 * 2
def baseEnd_838186 : Nat := 430392295869562827120259

theorem tailTrace_838186 : CollatzResearch.WordTrace tailWord_838186 prefixEnd_838186 430392295869562827120259 := by
  unfold tailWord_838186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7642788735350686904273603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20380769960935165078062941 7642788735350686904273603)
  ·
    refine ⟨11464183103026030356410405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7642788735350686904273603 11464183103026030356410405)
    ·
      refine ⟨2149534331817380691826951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11464183103026030356410405 2149534331817380691826951)
      ·
        refine ⟨3224301497726071037740427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2149534331817380691826951 3224301497726071037740427)
        ·
          refine ⟨4836452246589106556610641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3224301497726071037740427 4836452246589106556610641)
          ·
            refine ⟨3627339184941829917457981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4836452246589106556610641 3627339184941829917457981)
            ·
              refine ⟨1360252194353186219046743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3627339184941829917457981 1360252194353186219046743)
              ·
                refine ⟨2040378291529779328570115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360252194353186219046743 2040378291529779328570115)
                ·
                  refine ⟨3060567437294668992855173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040378291529779328570115 3060567437294668992855173)
                  ·
                    refine ⟨573856394492750436160345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3060567437294668992855173 573856394492750436160345)
                    ·
                      refine ⟨430392295869562827120259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 573856394492750436160345 430392295869562827120259)
                      ·
                        rfl

theorem cell23_838186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_838186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838186 prefixEnd_838186 := by exact prefixLift 838186
  have htrace : WordTrace (prefixWord ++ tailWord_838186) baseStart_838186 baseEnd_838186 := by
    simpa [prefixWord, tailWord_838186, baseEnd_838186] using wordTrace_append hprefix tailTrace_838186
  have hstable : (prefixWord ++ tailWord_838186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838186).length < 2 ^ (prefixWord ++ tailWord_838186).sum := by decide
  have hdescent : baseEnd_838186 < baseStart_838186 := by decide
  rcases family_descends (prefixWord ++ tailWord_838186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838206 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_838206 : Nat := 118140960795 + 838206 * 2 ^ 59
def prefixEnd_838206 : Nat := 4983230072969 + 3 ^ 40 * 838206 * 2
def baseEnd_838206 : Nat := 430402565482652748870167

theorem tailTrace_838206 : CollatzResearch.WordTrace tailWord_838206 prefixEnd_838206 430402565482652748870167 := by
  unfold tailWord_838206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3821485550166286379102809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20381256267553527355214981 3821485550166286379102809)
  ·
    refine ⟨2866114162624714784327107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3821485550166286379102809 2866114162624714784327107)
    ·
      refine ⟨4299171243937072176490661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2866114162624714784327107 4299171243937072176490661)
      ·
        refine ⟨806094608238201033091999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4299171243937072176490661 806094608238201033091999)
        ·
          refine ⟨1209141912357301549637999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806094608238201033091999 1209141912357301549637999)
          ·
            refine ⟨1813712868535952324456999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209141912357301549637999 1813712868535952324456999)
            ·
              refine ⟨2720569302803928486685499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813712868535952324456999 2720569302803928486685499)
              ·
                refine ⟨4080853954205892730028249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720569302803928486685499 4080853954205892730028249)
                ·
                  refine ⟨3060640465654419547521187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4080853954205892730028249 3060640465654419547521187)
                  ·
                    refine ⟨4590960698481629321281781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3060640465654419547521187 4590960698481629321281781)
                    ·
                      refine ⟨430402565482652748870167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4590960698481629321281781 430402565482652748870167)
                      ·
                        rfl

theorem cell23_838206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_838206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838206 prefixEnd_838206 := by exact prefixLift 838206
  have htrace : WordTrace (prefixWord ++ tailWord_838206) baseStart_838206 baseEnd_838206 := by
    simpa [prefixWord, tailWord_838206, baseEnd_838206] using wordTrace_append hprefix tailTrace_838206
  have hstable : (prefixWord ++ tailWord_838206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838206).length < 2 ^ (prefixWord ++ tailWord_838206).sum := by decide
  have hdescent : baseEnd_838206 < baseStart_838206 := by decide
  rcases family_descends (prefixWord ++ tailWord_838206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838222 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_838222 : Nat := 118140960795 + 838222 * 2 ^ 59
def prefixEnd_838222 : Nat := 4983230072969 + 3 ^ 40 * 838222 * 2
def baseEnd_838222 : Nat := 143470260391041562090031

theorem tailTrace_838222 : CollatzResearch.WordTrace tailWord_838222 prefixEnd_838222 143470260391041562090031 := by
  unfold tailWord_838222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3821558496159040720675615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20381645312848217176936613 3821558496159040720675615)
  ·
    refine ⟨5732337744238561081013423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3821558496159040720675615 5732337744238561081013423)
    ·
      refine ⟨8598506616357841621520135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5732337744238561081013423 8598506616357841621520135)
      ·
        refine ⟨12897759924536762432280203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8598506616357841621520135 12897759924536762432280203)
        ·
          refine ⟨19346639886805143648420305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12897759924536762432280203 19346639886805143648420305)
          ·
            refine ⟨14509979915103857736315229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19346639886805143648420305 14509979915103857736315229)
            ·
              refine ⟨5441242468163946651118211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14509979915103857736315229 5441242468163946651118211)
              ·
                refine ⟨8161863702245919976677317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5441242468163946651118211 8161863702245919976677317)
                ·
                  refine ⟨1530349444171109995626997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8161863702245919976677317 1530349444171109995626997)
                  ·
                    refine ⟨143470260391041562090031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1530349444171109995626997 143470260391041562090031)
                    ·
                      rfl

theorem cell23_838222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_838222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838222 prefixEnd_838222 := by exact prefixLift 838222
  have htrace : WordTrace (prefixWord ++ tailWord_838222) baseStart_838222 baseEnd_838222 := by
    simpa [prefixWord, tailWord_838222, baseEnd_838222] using wordTrace_append hprefix tailTrace_838222
  have hstable : (prefixWord ++ tailWord_838222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838222).length < 2 ^ (prefixWord ++ tailWord_838222).sum := by decide
  have hdescent : baseEnd_838222 < baseStart_838222 := by decide
  rcases family_descends (prefixWord ++ tailWord_838222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838226 : List Nat := [3, 2, 2, 1, 2, 1, 5, 2, 5]
def baseStart_838226 : Nat := 118140960795 + 838226 * 2 ^ 59
def prefixEnd_838226 : Nat := 4983230072969 + 3 ^ 40 * 838226 * 2
def baseEnd_838226 : Nat := 47823648343971407846675

theorem tailTrace_838226 : CollatzResearch.WordTrace tailWord_838226 prefixEnd_838226 47823648343971407846675 := by
  unfold tailWord_838226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7643153465314458612137633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20381742574171889632367021 7643153465314458612137633)
  ·
    refine ⟨5732365098985843959103225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7643153465314458612137633 5732365098985843959103225)
    ·
      refine ⟨4299273824239382969327419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5732365098985843959103225 4299273824239382969327419)
      ·
        refine ⟨6448910736359074453991129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4299273824239382969327419 6448910736359074453991129)
        ·
          refine ⟨4836683052269305840493347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6448910736359074453991129 4836683052269305840493347)
          ·
            refine ⟨7255024578403958760740021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836683052269305840493347 7255024578403958760740021)
            ·
              refine ⟨680158554225371133819377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7255024578403958760740021 680158554225371133819377)
              ·
                refine ⟨510118915669028350364533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 680158554225371133819377 510118915669028350364533)
                ·
                  refine ⟨47823648343971407846675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 510118915669028350364533 47823648343971407846675)
                  ·
                    rfl

theorem cell23_838226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_838226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838226 prefixEnd_838226 := by exact prefixLift 838226
  have htrace : WordTrace (prefixWord ++ tailWord_838226) baseStart_838226 baseEnd_838226 := by
    simpa [prefixWord, tailWord_838226, baseEnd_838226] using wordTrace_append hprefix tailTrace_838226
  have hstable : (prefixWord ++ tailWord_838226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838226).length < 2 ^ (prefixWord ++ tailWord_838226).sum := by decide
  have hdescent : baseEnd_838226 < baseStart_838226 := by decide
  rcases family_descends (prefixWord ++ tailWord_838226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838279 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_838279 : Nat := 118140960795 + 838279 * 2 ^ 59
def prefixEnd_838279 : Nat := 4983230072969 + 3 ^ 40 * 838279 * 2
def baseEnd_838279 : Nat := 430440049570430963257331

theorem tailTrace_838279 : CollatzResearch.WordTrace tailWord_838279 prefixEnd_838279 430440049570430963257331 := by
  unfold tailWord_838279
  simp only [CollatzResearch.WordTrace]
  refine ⟨30574546930065824500229891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20383031286710549666819927 30574546930065824500229891)
  ·
    refine ⟨45861820395098736750344837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30574546930065824500229891 45861820395098736750344837)
    ·
      refine ⟨8599091324081013140689657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45861820395098736750344837 8599091324081013140689657)
      ·
        refine ⟨6449318493060759855517243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8599091324081013140689657 6449318493060759855517243)
        ·
          refine ⟨9673977739591139783275865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6449318493060759855517243 9673977739591139783275865)
          ·
            refine ⟨7255483304693354837456899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9673977739591139783275865 7255483304693354837456899)
            ·
              refine ⟨10883224957040032256185349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7255483304693354837456899 10883224957040032256185349)
              ·
                refine ⟨2040604679445006048034753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10883224957040032256185349 2040604679445006048034753)
                ·
                  refine ⟨1530453509583754536026065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2040604679445006048034753 1530453509583754536026065)
                  ·
                    refine ⟨1147840132187815902019549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1530453509583754536026065 1147840132187815902019549)
                    ·
                      refine ⟨430440049570430963257331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1147840132187815902019549 430440049570430963257331)
                      ·
                        rfl

theorem cell23_838279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_838279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838279 prefixEnd_838279 := by exact prefixLift 838279
  have htrace : WordTrace (prefixWord ++ tailWord_838279) baseStart_838279 baseEnd_838279 := by
    simpa [prefixWord, tailWord_838279, baseEnd_838279] using wordTrace_append hprefix tailTrace_838279
  have hstable : (prefixWord ++ tailWord_838279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838279).length < 2 ^ (prefixWord ++ tailWord_838279).sum := by decide
  have hdescent : baseEnd_838279 < baseStart_838279 := by decide
  rcases family_descends (prefixWord ++ tailWord_838279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838322 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_838322 : Nat := 118140960795 + 838322 * 2 ^ 59
def prefixEnd_838322 : Nat := 4983230072969 + 3 ^ 40 * 838322 * 2
def baseEnd_838322 : Nat := 430462129238574295019633

theorem tailTrace_838322 : CollatzResearch.WordTrace tailWord_838322 prefixEnd_838322 430462129238574295019633 := by
  unfold tailWord_838322
  simp only [CollatzResearch.WordTrace]
  refine ⟨7644028817227510711011305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20384076845940028562696813 7644028817227510711011305)
  ·
    refine ⟨5733021612920633033258479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7644028817227510711011305 5733021612920633033258479)
    ·
      refine ⟨8599532419380949549887719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5733021612920633033258479 8599532419380949549887719)
      ·
        refine ⟨12899298629071424324831579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8599532419380949549887719 12899298629071424324831579)
        ·
          refine ⟨19348947943607136487247369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12899298629071424324831579 19348947943607136487247369)
          ·
            refine ⟨14511710957705352365435527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19348947943607136487247369 14511710957705352365435527)
            ·
              refine ⟨21767566436558028548153291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14511710957705352365435527 21767566436558028548153291)
              ·
                refine ⟨32651349654837042822229937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21767566436558028548153291 32651349654837042822229937)
                ·
                  refine ⟨24488512241127782116672453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32651349654837042822229937 24488512241127782116672453)
                  ·
                    refine ⟨4591596045211459146876085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24488512241127782116672453 4591596045211459146876085)
                    ·
                      refine ⟨430462129238574295019633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4591596045211459146876085 430462129238574295019633)
                      ·
                        rfl

theorem cell23_838322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_838322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838322 prefixEnd_838322 := by exact prefixLift 838322
  have htrace : WordTrace (prefixWord ++ tailWord_838322) baseStart_838322 baseEnd_838322 := by
    simpa [prefixWord, tailWord_838322, baseEnd_838322] using wordTrace_append hprefix tailTrace_838322
  have hstable : (prefixWord ++ tailWord_838322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838322).length < 2 ^ (prefixWord ++ tailWord_838322).sum := by decide
  have hdescent : baseEnd_838322 < baseStart_838322 := by decide
  rcases family_descends (prefixWord ++ tailWord_838322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838359 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 1, 6]
def baseStart_838359 : Nat := 118140960795 + 838359 * 2 ^ 59
def prefixEnd_838359 : Nat := 4983230072969 + 3 ^ 40 * 838359 * 2
def baseEnd_838359 : Nat := 143493709340930216752321

theorem tailTrace_838359 : CollatzResearch.WordTrace tailWord_838359 prefixEnd_838359 143493709340930216752321 := by
  unfold tailWord_838359
  simp only [CollatzResearch.WordTrace]
  refine ⟨30577464769775998163142131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20384976513183998775428087 30577464769775998163142131)
  ·
    refine ⟨45866197154663997244713197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30577464769775998163142131 45866197154663997244713197)
    ·
      refine ⟨17199823932998998966767449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45866197154663997244713197 17199823932998998966767449)
      ·
        refine ⟨12899867949749249225075587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17199823932998998966767449 12899867949749249225075587)
        ·
          refine ⟨19349801924623873837613381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12899867949749249225075587 19349801924623873837613381)
          ·
            refine ⟨3628087860866976344552509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19349801924623873837613381 3628087860866976344552509)
            ·
              refine ⟨1360532947825116129207191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3628087860866976344552509 1360532947825116129207191)
              ·
                refine ⟨2040799421737674193810787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360532947825116129207191 2040799421737674193810787)
                ·
                  refine ⟨3061199132606511290716181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040799421737674193810787 3061199132606511290716181)
                  ·
                    refine ⟨143493709340930216752321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3061199132606511290716181 143493709340930216752321)
                    ·
                      rfl

theorem cell23_838359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_838359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838359 prefixEnd_838359 := by exact prefixLift 838359
  have htrace : WordTrace (prefixWord ++ tailWord_838359) baseStart_838359 baseEnd_838359 := by
    simpa [prefixWord, tailWord_838359, baseEnd_838359] using wordTrace_append hprefix tailTrace_838359
  have hstable : (prefixWord ++ tailWord_838359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838359).length < 2 ^ (prefixWord ++ tailWord_838359).sum := by decide
  have hdescent : baseEnd_838359 < baseStart_838359 := by decide
  rcases family_descends (prefixWord ++ tailWord_838359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838386 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_838386 : Nat := 118140960795 + 838386 * 2 ^ 59
def prefixEnd_838386 : Nat := 4983230072969 + 3 ^ 40 * 838386 * 2
def baseEnd_838386 : Nat := 430494992000462044619339

theorem tailTrace_838386 : CollatzResearch.WordTrace tailWord_838386 prefixEnd_838386 430494992000462044619339 := by
  unfold tailWord_838386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7644612385169545443593753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20385633027118787849583341 7644612385169545443593753)
  ·
    refine ⟨5733459288877159082695315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7644612385169545443593753 5733459288877159082695315)
    ·
      refine ⟨8600188933315738624042973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5733459288877159082695315 8600188933315738624042973)
      ·
        refine ⟨3225070849993401984016115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8600188933315738624042973 3225070849993401984016115)
        ·
          refine ⟨4837606274990102976024173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3225070849993401984016115 4837606274990102976024173)
          ·
            refine ⟨1814102353121288616009065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4837606274990102976024173 1814102353121288616009065)
            ·
              refine ⟨1360576764840966462006799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1814102353121288616009065 1360576764840966462006799)
              ·
                refine ⟨2040865147261449693010199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360576764840966462006799 2040865147261449693010199)
                ·
                  refine ⟨3061297720892174539515299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040865147261449693010199 3061297720892174539515299)
                  ·
                    refine ⟨4591946581338261809272949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3061297720892174539515299 4591946581338261809272949)
                    ·
                      refine ⟨430494992000462044619339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4591946581338261809272949 430494992000462044619339)
                      ·
                        rfl

theorem cell23_838386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_838386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838386 prefixEnd_838386 := by exact prefixLift 838386
  have htrace : WordTrace (prefixWord ++ tailWord_838386) baseStart_838386 baseEnd_838386 := by
    simpa [prefixWord, tailWord_838386, baseEnd_838386] using wordTrace_append hprefix tailTrace_838386
  have hstable : (prefixWord ++ tailWord_838386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838386).length < 2 ^ (prefixWord ++ tailWord_838386).sum := by decide
  have hdescent : baseEnd_838386 < baseStart_838386 := by decide
  rcases family_descends (prefixWord ++ tailWord_838386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838449 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 2, 6]
def baseStart_838449 : Nat := 118140960795 + 838449 * 2 ^ 59
def prefixEnd_838449 : Nat := 4983230072969 + 3 ^ 40 * 838449 * 2
def baseEnd_838449 : Nat := 143509113760565099377183

theorem tailTrace_838449 : CollatzResearch.WordTrace tailWord_838449 prefixEnd_838449 143509113760565099377183 := by
  unfold tailWord_838449
  simp only [CollatzResearch.WordTrace]
  refine ⟨30580747339449943533918401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20387164892966629022612267 30580747339449943533918401)
  ·
    refine ⟨22935560504587457650438801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30580747339449943533918401 22935560504587457650438801)
    ·
      refine ⟨17201670378440593237829101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22935560504587457650438801 17201670378440593237829101)
      ·
        refine ⟨6450626391915222464185913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17201670378440593237829101 6450626391915222464185913)
        ·
          refine ⟨4837969793936416848139435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6450626391915222464185913 4837969793936416848139435)
          ·
            refine ⟨7256954690904625272209153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837969793936416848139435 7256954690904625272209153)
            ·
              refine ⟨5442716018178468954156865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7256954690904625272209153 5442716018178468954156865)
              ·
                refine ⟨4082037013633851715617649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5442716018178468954156865 4082037013633851715617649)
                ·
                  refine ⟨3061527760225388786713237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4082037013633851715617649 3061527760225388786713237)
                  ·
                    refine ⟨143509113760565099377183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3061527760225388786713237 143509113760565099377183)
                    ·
                      rfl

theorem cell23_838449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_838449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838449 prefixEnd_838449 := by exact prefixLift 838449
  have htrace : WordTrace (prefixWord ++ tailWord_838449) baseStart_838449 baseEnd_838449 := by
    simpa [prefixWord, tailWord_838449, baseEnd_838449] using wordTrace_append hprefix tailTrace_838449
  have hstable : (prefixWord ++ tailWord_838449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838449).length < 2 ^ (prefixWord ++ tailWord_838449).sum := by decide
  have hdescent : baseEnd_838449 < baseStart_838449 := by decide
  rcases family_descends (prefixWord ++ tailWord_838449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838456 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 2]
def baseStart_838456 : Nat := 118140960795 + 838456 * 2 ^ 59
def prefixEnd_838456 : Nat := 4983230072969 + 3 ^ 40 * 838456 * 2
def baseEnd_838456 : Nat := 430530935646276770744017

theorem tailTrace_838456 : CollatzResearch.WordTrace tailWord_838456 prefixEnd_838456 430530935646276770744017 := by
  unfold tailWord_838456
  simp only [CollatzResearch.WordTrace]
  refine ⟨15290501325212291864711611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20387335100283055819615481 15290501325212291864711611)
  ·
    refine ⟨22935751987818437797067417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15290501325212291864711611 22935751987818437797067417)
    ·
      refine ⟨17201813990863828347800563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22935751987818437797067417 17201813990863828347800563)
      ·
        refine ⟨25802720986295742521700845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17201813990863828347800563 25802720986295742521700845)
        ·
          refine ⟨9676020369860903445637817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25802720986295742521700845 9676020369860903445637817)
          ·
            refine ⟨7257015277395677584228363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9676020369860903445637817 7257015277395677584228363)
            ·
              refine ⟨10885522916093516376342545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7257015277395677584228363 10885522916093516376342545)
              ·
                refine ⟨8164142187070137282256909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10885522916093516376342545 8164142187070137282256909)
                ·
                  refine ⟨3061553320151301480846341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8164142187070137282256909 3061553320151301480846341)
                  ·
                    refine ⟨574041247528369027658689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3061553320151301480846341 574041247528369027658689)
                    ·
                      refine ⟨430530935646276770744017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574041247528369027658689 430530935646276770744017)
                      ·
                        rfl

theorem cell23_838456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 3, 4, 2].length) (baseStart_838456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838456 prefixEnd_838456 := by exact prefixLift 838456
  have htrace : WordTrace (prefixWord ++ tailWord_838456) baseStart_838456 baseEnd_838456 := by
    simpa [prefixWord, tailWord_838456, baseEnd_838456] using wordTrace_append hprefix tailTrace_838456
  have hstable : (prefixWord ++ tailWord_838456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838456).length < 2 ^ (prefixWord ++ tailWord_838456).sum := by decide
  have hdescent : baseEnd_838456 < baseStart_838456 := by decide
  rcases family_descends (prefixWord ++ tailWord_838456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838473 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 1, 4, 2]
def baseStart_838473 : Nat := 118140960795 + 838473 * 2 ^ 59
def prefixEnd_838473 : Nat := 4983230072969 + 3 ^ 40 * 838473 * 2
def baseEnd_838473 : Nat := 430539664817403204231439

theorem tailTrace_838473 : CollatzResearch.WordTrace tailWord_838473 prefixEnd_838473 430539664817403204231439 := by
  unfold tailWord_838473
  simp only [CollatzResearch.WordTrace]
  refine ⟨30581622691362995632792073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20387748460908663755194715 30581622691362995632792073)
  ·
    refine ⟨22936217018522246724594055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30581622691362995632792073 22936217018522246724594055)
    ·
      refine ⟨34404325527783370086891083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22936217018522246724594055 34404325527783370086891083)
      ·
        refine ⟨51606488291675055130336625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34404325527783370086891083 51606488291675055130336625)
        ·
          refine ⟨38704866218756291347752469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51606488291675055130336625 38704866218756291347752469)
          ·
            refine ⟨1814290604004201156925897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38704866218756291347752469 1814290604004201156925897)
            ·
              refine ⟨1360717953003150867694423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1814290604004201156925897 1360717953003150867694423)
              ·
                refine ⟨2041076929504726301541635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360717953003150867694423 2041076929504726301541635)
                ·
                  refine ⟨3061615394257089452312453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2041076929504726301541635 3061615394257089452312453)
                  ·
                    refine ⟨574052886423204272308585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3061615394257089452312453 574052886423204272308585)
                    ·
                      refine ⟨430539664817403204231439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574052886423204272308585 430539664817403204231439)
                      ·
                        rfl

theorem cell23_838473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 4, 2].length) (baseStart_838473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838473 prefixEnd_838473 := by exact prefixLift 838473
  have htrace : WordTrace (prefixWord ++ tailWord_838473) baseStart_838473 baseEnd_838473 := by
    simpa [prefixWord, tailWord_838473, baseEnd_838473] using wordTrace_append hprefix tailTrace_838473
  have hstable : (prefixWord ++ tailWord_838473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838473).length < 2 ^ (prefixWord ++ tailWord_838473).sum := by decide
  have hdescent : baseEnd_838473 < baseStart_838473 := by decide
  rcases family_descends (prefixWord ++ tailWord_838473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838519 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_838519 : Nat := 118140960795 + 838519 * 2 ^ 59
def prefixEnd_838519 : Nat := 4983230072969 + 3 ^ 40 * 838519 * 2
def baseEnd_838519 : Nat := 430563284927510024256227

theorem tailTrace_838519 : CollatzResearch.WordTrace tailWord_838519 prefixEnd_838519 430563284927510024256227 := by
  unfold tailWord_838519
  simp only [CollatzResearch.WordTrace]
  refine ⟨30583300449196345488966611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20388866966130896992644407 30583300449196345488966611)
  ·
    refine ⟨45874950673794518233449917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30583300449196345488966611 45874950673794518233449917)
    ·
      refine ⟨17203106502672944337543719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45874950673794518233449917 17203106502672944337543719)
      ·
        refine ⟨25804659754009416506315579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17203106502672944337543719 25804659754009416506315579)
        ·
          refine ⟨38706989631014124759473369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25804659754009416506315579 38706989631014124759473369)
          ·
            refine ⟨29030242223260593569605027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38706989631014124759473369 29030242223260593569605027)
            ·
              refine ⟨43545363334890890354407541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29030242223260593569605027 43545363334890890354407541)
              ·
                refine ⟨4082377812646020970725707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43545363334890890354407541 4082377812646020970725707)
                ·
                  refine ⟨6123566718969031456088561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4082377812646020970725707 6123566718969031456088561)
                  ·
                    refine ⟨4592675039226773592066421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6123566718969031456088561 4592675039226773592066421)
                    ·
                      refine ⟨430563284927510024256227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4592675039226773592066421 430563284927510024256227)
                      ·
                        rfl

theorem cell23_838519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_838519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838519 prefixEnd_838519 := by exact prefixLift 838519
  have htrace : WordTrace (prefixWord ++ tailWord_838519) baseStart_838519 baseEnd_838519 := by
    simpa [prefixWord, tailWord_838519, baseEnd_838519] using wordTrace_append hprefix tailTrace_838519
  have hstable : (prefixWord ++ tailWord_838519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838519).length < 2 ^ (prefixWord ++ tailWord_838519).sum := by decide
  have hdescent : baseEnd_838519 < baseStart_838519 := by decide
  rcases family_descends (prefixWord ++ tailWord_838519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838569 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 8]
def baseStart_838569 : Nat := 118140960795 + 838569 * 2 ^ 59
def prefixEnd_838569 : Nat := 4983230072969 + 3 ^ 40 * 838569 * 2
def baseEnd_838569 : Nat := 47843217662248314292333

theorem tailTrace_838569 : CollatzResearch.WordTrace tailWord_838569 prefixEnd_838569 47843217662248314292333 := by
  unfold tailWord_838569
  simp only [CollatzResearch.WordTrace]
  refine ⟨30585124099015204028286761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20390082732676802685524507 30585124099015204028286761)
  ·
    refine ⟨22938843074261403021215071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30585124099015204028286761 22938843074261403021215071)
    ·
      refine ⟨34408264611392104531822607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22938843074261403021215071 34408264611392104531822607)
      ·
        refine ⟨51612396917088156797733911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34408264611392104531822607 51612396917088156797733911)
        ·
          refine ⟨77418595375632235196600867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51612396917088156797733911 77418595375632235196600867)
          ·
            refine ⟨116127893063448352794901301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77418595375632235196600867 116127893063448352794901301)
            ·
              refine ⟨10886989974698283074521997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116127893063448352794901301 10886989974698283074521997)
              ·
                refine ⟨4082621240511856152945749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10886989974698283074521997 4082621240511856152945749)
                ·
                  refine ⟨47843217662248314292333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4082621240511856152945749 47843217662248314292333)
                  ·
                    rfl

theorem cell23_838569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 8].length) (baseStart_838569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838569 prefixEnd_838569 := by exact prefixLift 838569
  have htrace : WordTrace (prefixWord ++ tailWord_838569) baseStart_838569 baseEnd_838569 := by
    simpa [prefixWord, tailWord_838569, baseEnd_838569] using wordTrace_append hprefix tailTrace_838569
  have hstable : (prefixWord ++ tailWord_838569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838569).length < 2 ^ (prefixWord ++ tailWord_838569).sum := by decide
  have hdescent : baseEnd_838569 < baseStart_838569 := by decide
  rcases family_descends (prefixWord ++ tailWord_838569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838586 : List Nat := [3, 1, 1, 1, 2, 1, 5, 3, 6]
def baseStart_838586 : Nat := 118140960795 + 838586 * 2 ^ 59
def prefixEnd_838586 : Nat := 4983230072969 + 3 ^ 40 * 838586 * 2
def baseEnd_838586 : Nat := 47844187570151251346491

theorem tailTrace_838586 : CollatzResearch.WordTrace tailWord_838586 prefixEnd_838586 47844187570151251346491 := by
  unfold tailWord_838586
  simp only [CollatzResearch.WordTrace]
  refine ⟨7646436034988403982913903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20390496093302410621103741 7646436034988403982913903)
  ·
    refine ⟨11469654052482605974370855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7646436034988403982913903 11469654052482605974370855)
    ·
      refine ⟨17204481078723908961556283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11469654052482605974370855 17204481078723908961556283)
      ·
        refine ⟨25806721618085863442334425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17204481078723908961556283 25806721618085863442334425)
        ·
          refine ⟨19355041213564397581750819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25806721618085863442334425 19355041213564397581750819)
          ·
            refine ⟨29032561820346596372626229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19355041213564397581750819 29032561820346596372626229)
            ·
              refine ⟨2721802670657493409933709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29032561820346596372626229 2721802670657493409933709)
              ·
                refine ⟨1020676001496560028725141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2721802670657493409933709 1020676001496560028725141)
                ·
                  refine ⟨47844187570151251346491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1020676001496560028725141 47844187570151251346491)
                  ·
                    rfl

theorem cell23_838586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_838586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838586 prefixEnd_838586 := by exact prefixLift 838586
  have htrace : WordTrace (prefixWord ++ tailWord_838586) baseStart_838586 baseEnd_838586 := by
    simpa [prefixWord, tailWord_838586, baseEnd_838586] using wordTrace_append hprefix tailTrace_838586
  have hstable : (prefixWord ++ tailWord_838586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838586).length < 2 ^ (prefixWord ++ tailWord_838586).sum := by decide
  have hdescent : baseEnd_838586 < baseStart_838586 := by decide
  rcases family_descends (prefixWord ++ tailWord_838586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838600 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_838600 : Nat := 118140960795 + 838600 * 2 ^ 59
def prefixEnd_838600 : Nat := 4983230072969 + 3 ^ 40 * 838600 * 2
def baseEnd_838600 : Nat := 430604876860524207343355

theorem tailTrace_838600 : CollatzResearch.WordTrace tailWord_838600 prefixEnd_838600 430604876860524207343355 := by
  unfold tailWord_838600
  simp only [CollatzResearch.WordTrace]
  refine ⟨15293127380951448161332627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20390836507935264215110169 15293127380951448161332627)
  ·
    refine ⟨22939691071427172241998941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15293127380951448161332627 22939691071427172241998941)
    ·
      refine ⟨8602384151785189590749603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22939691071427172241998941 8602384151785189590749603)
      ·
        refine ⟨12903576227677784386124405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8602384151785189590749603 12903576227677784386124405)
        ·
          refine ⟨1209710271344792286199163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12903576227677784386124405 1209710271344792286199163)
          ·
            refine ⟨1814565407017188429298745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209710271344792286199163 1814565407017188429298745)
            ·
              refine ⟨1360924055262891321974059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1814565407017188429298745 1360924055262891321974059)
              ·
                refine ⟨2041386082894336982961089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360924055262891321974059 2041386082894336982961089)
                ·
                  refine ⟨1531039562170752737220817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2041386082894336982961089 1531039562170752737220817)
                  ·
                    refine ⟨1148279671628064552915613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1531039562170752737220817 1148279671628064552915613)
                    ·
                      refine ⟨430604876860524207343355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1148279671628064552915613 430604876860524207343355)
                      ·
                        rfl

theorem cell23_838600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_838600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838600 prefixEnd_838600 := by exact prefixLift 838600
  have htrace : WordTrace (prefixWord ++ tailWord_838600) baseStart_838600 baseEnd_838600 := by
    simpa [prefixWord, tailWord_838600, baseEnd_838600] using wordTrace_append hprefix tailTrace_838600
  have hstable : (prefixWord ++ tailWord_838600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838600).length < 2 ^ (prefixWord ++ tailWord_838600).sum := by decide
  have hdescent : baseEnd_838600 < baseStart_838600 := by decide
  rcases family_descends (prefixWord ++ tailWord_838600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838619 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 10]
def baseStart_838619 : Nat := 118140960795 + 838619 * 2 ^ 59
def prefixEnd_838619 : Nat := 4983230072969 + 3 ^ 40 * 838619 * 2
def baseEnd_838619 : Nat := 430614632992959633005767

theorem tailTrace_838619 : CollatzResearch.WordTrace tailWord_838619 prefixEnd_838619 430614632992959633005767 := by
  unfold tailWord_838619
  simp only [CollatzResearch.WordTrace]
  refine ⟨30586947748834062567606911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20391298499222708378404607 30586947748834062567606911)
  ·
    refine ⟨45880421623251093851410367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30586947748834062567606911 45880421623251093851410367)
    ·
      refine ⟨68820632434876640777115551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45880421623251093851410367 68820632434876640777115551)
      ·
        refine ⟨103230948652314961165673327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68820632434876640777115551 103230948652314961165673327)
        ·
          refine ⟨154846422978472441748509991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103230948652314961165673327 154846422978472441748509991)
          ·
            refine ⟨232269634467708662622764987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154846422978472441748509991 232269634467708662622764987)
            ·
              refine ⟨348404451701562993934147481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232269634467708662622764987 348404451701562993934147481)
              ·
                refine ⟨261303338776172245450610611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348404451701562993934147481 261303338776172245450610611)
                ·
                  refine ⟨391955008164258368175915917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261303338776172245450610611 391955008164258368175915917)
                  ·
                    refine ⟨146983128061596888065968469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 391955008164258368175915917 146983128061596888065968469)
                    ·
                      refine ⟨430614632992959633005767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 146983128061596888065968469 430614632992959633005767)
                      ·
                        rfl

theorem cell23_838619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_838619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838619 prefixEnd_838619 := by exact prefixLift 838619
  have htrace : WordTrace (prefixWord ++ tailWord_838619) baseStart_838619 baseEnd_838619 := by
    simpa [prefixWord, tailWord_838619, baseEnd_838619] using wordTrace_append hprefix tailTrace_838619
  have hstable : (prefixWord ++ tailWord_838619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838619).length < 2 ^ (prefixWord ++ tailWord_838619).sum := by decide
  have hdescent : baseEnd_838619 < baseStart_838619 := by decide
  rcases family_descends (prefixWord ++ tailWord_838619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838653 : List Nat := [1, 4, 1, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_838653 : Nat := 118140960795 + 838653 * 2 ^ 59
def prefixEnd_838653 : Nat := 4983230072969 + 3 ^ 40 * 838653 * 2
def baseEnd_838653 : Nat := 430632091335212499980611

theorem tailTrace_838653 : CollatzResearch.WordTrace tailWord_838653 prefixEnd_838653 430632091335212499980611 := by
  unfold tailWord_838653
  simp only [CollatzResearch.WordTrace]
  refine ⟨30588187830710886374344613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20392125220473924249563075 30588187830710886374344613)
  ·
    refine ⟨5735285218258291195189615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30588187830710886374344613 5735285218258291195189615)
    ·
      refine ⟨8602927827387436792784423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5735285218258291195189615 8602927827387436792784423)
      ·
        refine ⟨12904391741081155189176635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8602927827387436792784423 12904391741081155189176635)
        ·
          refine ⟨19356587611621732783764953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12904391741081155189176635 19356587611621732783764953)
          ·
            refine ⟨14517440708716299587823715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19356587611621732783764953 14517440708716299587823715)
            ·
              refine ⟨21776161063074449381735573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14517440708716299587823715 21776161063074449381735573)
              ·
                refine ⟨1020757549831614814768855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21776161063074449381735573 1020757549831614814768855)
                ·
                  refine ⟨1531136324747422222153283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020757549831614814768855 1531136324747422222153283)
                  ·
                    refine ⟨2296704487121133333229925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1531136324747422222153283 2296704487121133333229925)
                    ·
                      refine ⟨430632091335212499980611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2296704487121133333229925 430632091335212499980611)
                      ·
                        rfl

theorem cell23_838653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_838653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838653 prefixEnd_838653 := by exact prefixLift 838653
  have htrace : WordTrace (prefixWord ++ tailWord_838653) baseStart_838653 baseEnd_838653 := by
    simpa [prefixWord, tailWord_838653, baseEnd_838653] using wordTrace_append hprefix tailTrace_838653
  have hstable : (prefixWord ++ tailWord_838653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838653).length < 2 ^ (prefixWord ++ tailWord_838653).sum := by decide
  have hdescent : baseEnd_838653 < baseStart_838653 := by decide
  rcases family_descends (prefixWord ++ tailWord_838653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838657 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_838657 : Nat := 118140960795 + 838657 * 2 ^ 59
def prefixEnd_838657 : Nat := 4983230072969 + 3 ^ 40 * 838657 * 2
def baseEnd_838657 : Nat := 430634145257830484330593

theorem tailTrace_838657 : CollatzResearch.WordTrace tailWord_838657 prefixEnd_838657 430634145257830484330593 := by
  unfold tailWord_838657
  simp only [CollatzResearch.WordTrace]
  refine ⟨30588333722696395057490225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20392222481797596704993483 30588333722696395057490225)
  ·
    refine ⟨22941250292022296293117669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30588333722696395057490225 22941250292022296293117669)
    ·
      refine ⟨4301484429754180554959563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22941250292022296293117669 4301484429754180554959563)
      ·
        refine ⟨6452226644631270832439345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4301484429754180554959563 6452226644631270832439345)
        ·
          refine ⟨4839169983473453124329509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6452226644631270832439345 4839169983473453124329509)
          ·
            refine ⟨907344371901272460811783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4839169983473453124329509 907344371901272460811783)
            ·
              refine ⟨1361016557851908691217675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907344371901272460811783 1361016557851908691217675)
              ·
                refine ⟨2041524836777863036826513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361016557851908691217675 2041524836777863036826513)
                ·
                  refine ⟨1531143627583397277619885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2041524836777863036826513 1531143627583397277619885)
                  ·
                    refine ⟨574178860343773979107457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531143627583397277619885 574178860343773979107457)
                    ·
                      refine ⟨430634145257830484330593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574178860343773979107457 430634145257830484330593)
                      ·
                        rfl

theorem cell23_838657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_838657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838657 prefixEnd_838657 := by exact prefixLift 838657
  have htrace : WordTrace (prefixWord ++ tailWord_838657) baseStart_838657 baseEnd_838657 := by
    simpa [prefixWord, tailWord_838657, baseEnd_838657] using wordTrace_append hprefix tailTrace_838657
  have hstable : (prefixWord ++ tailWord_838657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838657).length < 2 ^ (prefixWord ++ tailWord_838657).sum := by decide
  have hdescent : baseEnd_838657 < baseStart_838657 := by decide
  rcases family_descends (prefixWord ++ tailWord_838657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838663 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 4, 4]
def baseStart_838663 : Nat := 118140960795 + 838663 * 2 ^ 59
def prefixEnd_838663 : Nat := 4983230072969 + 3 ^ 40 * 838663 * 2
def baseEnd_838663 : Nat := 143545742047252486951855

theorem tailTrace_838663 : CollatzResearch.WordTrace tailWord_838663 prefixEnd_838663 143545742047252486951855 := by
  unfold tailWord_838663
  simp only [CollatzResearch.WordTrace]
  refine ⟨30588552560674658082208643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20392368373783105388139095 30588552560674658082208643)
  ·
    refine ⟨45882828841011987123312965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30588552560674658082208643 45882828841011987123312965)
    ·
      refine ⟨8603030407689747585621181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45882828841011987123312965 8603030407689747585621181)
      ·
        refine ⟨3226136402883655344607943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8603030407689747585621181 3226136402883655344607943)
        ·
          refine ⟨4839204604325483016911915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3226136402883655344607943 4839204604325483016911915)
          ·
            refine ⟨7258806906488224525367873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4839204604325483016911915 7258806906488224525367873)
            ·
              refine ⟨5444105179866168394025905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7258806906488224525367873 5444105179866168394025905)
              ·
                refine ⟨4083078884899626295519429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5444105179866168394025905 4083078884899626295519429)
                ·
                  refine ⟨765577290918679930409893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4083078884899626295519429 765577290918679930409893)
                  ·
                    refine ⟨143545742047252486951855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 765577290918679930409893 143545742047252486951855)
                    ·
                      rfl

theorem cell23_838663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_838663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838663 prefixEnd_838663 := by exact prefixLift 838663
  have htrace : WordTrace (prefixWord ++ tailWord_838663) baseStart_838663 baseEnd_838663 := by
    simpa [prefixWord, tailWord_838663, baseEnd_838663] using wordTrace_append hprefix tailTrace_838663
  have hstable : (prefixWord ++ tailWord_838663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838663).length < 2 ^ (prefixWord ++ tailWord_838663).sum := by decide
  have hdescent : baseEnd_838663 < baseStart_838663 := by decide
  rcases family_descends (prefixWord ++ tailWord_838663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838670 : List Nat := [4, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_838670 : Nat := 118140960795 + 838670 * 2 ^ 59
def prefixEnd_838670 : Nat := 4983230072969 + 3 ^ 40 * 838670 * 2
def baseEnd_838670 : Nat := 430640820506338933468033

theorem tailTrace_838670 : CollatzResearch.WordTrace tailWord_838670 prefixEnd_838670 430640820506338933468033 := by
  unfold tailWord_838670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3823600983956162284714183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20392538581099532185142309 3823600983956162284714183)
  ·
    refine ⟨5735401475934243427071275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3823600983956162284714183 5735401475934243427071275)
    ·
      refine ⟨8603102213901365140606913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5735401475934243427071275 8603102213901365140606913)
      ·
        refine ⟨6452326660426023855455185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8603102213901365140606913 6452326660426023855455185)
        ·
          refine ⟨4839244995319517891591389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6452326660426023855455185 4839244995319517891591389)
          ·
            refine ⟨1814716873244819209346771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4839244995319517891591389 1814716873244819209346771)
            ·
              refine ⟨2722075309867228814020157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814716873244819209346771 2722075309867228814020157)
              ·
                refine ⟨1020778241200210805257559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2722075309867228814020157 1020778241200210805257559)
                ·
                  refine ⟨1531167361800316207886339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1020778241200210805257559 1531167361800316207886339)
                  ·
                    refine ⟨2296751042700474311829509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1531167361800316207886339 2296751042700474311829509)
                    ·
                      refine ⟨430640820506338933468033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2296751042700474311829509 430640820506338933468033)
                      ·
                        rfl

theorem cell23_838670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_838670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838670 prefixEnd_838670 := by exact prefixLift 838670
  have htrace : WordTrace (prefixWord ++ tailWord_838670) baseStart_838670 baseEnd_838670 := by
    simpa [prefixWord, tailWord_838670, baseEnd_838670] using wordTrace_append hprefix tailTrace_838670
  have hstable : (prefixWord ++ tailWord_838670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838670).length < 2 ^ (prefixWord ++ tailWord_838670).sum := by decide
  have hdescent : baseEnd_838670 < baseStart_838670 := by decide
  rcases family_descends (prefixWord ++ tailWord_838670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838680 : List Nat := [2, 1, 2, 3, 2, 2, 3, 2, 2, 4]
def baseStart_838680 : Nat := 118140960795 + 838680 * 2 ^ 59
def prefixEnd_838680 : Nat := 4983230072969 + 3 ^ 40 * 838680 * 2
def baseEnd_838680 : Nat := 143548651770961298114329

theorem tailTrace_838680 : CollatzResearch.WordTrace tailWord_838680 prefixEnd_838680 143548651770961298114329 := by
  unfold tailWord_838680
  simp only [CollatzResearch.WordTrace]
  refine ⟨15294586300806534992788747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20392781734408713323718329 15294586300806534992788747)
  ·
    refine ⟨22941879451209802489183121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15294586300806534992788747 22941879451209802489183121)
    ·
      refine ⟨17206409588407351866887341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22941879451209802489183121 17206409588407351866887341)
      ·
        refine ⟨6452403595652756950082753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17206409588407351866887341 6452403595652756950082753)
        ·
          refine ⟨4839302696739567712562065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6452403595652756950082753 4839302696739567712562065)
          ·
            refine ⟨3629477022554675784421549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4839302696739567712562065 3629477022554675784421549)
            ·
              refine ⟨1361053883458003419158081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3629477022554675784421549 1361053883458003419158081)
              ·
                refine ⟨1020790412593502564368561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361053883458003419158081 1020790412593502564368561)
                ·
                  refine ⟨765592809445126923276421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1020790412593502564368561 765592809445126923276421)
                  ·
                    refine ⟨143548651770961298114329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 765592809445126923276421 143548651770961298114329)
                    ·
                      rfl

theorem cell23_838680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_838680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838680 prefixEnd_838680 := by exact prefixLift 838680
  have htrace : WordTrace (prefixWord ++ tailWord_838680) baseStart_838680 baseEnd_838680 := by
    simpa [prefixWord, tailWord_838680, baseEnd_838680] using wordTrace_append hprefix tailTrace_838680
  have hstable : (prefixWord ++ tailWord_838680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838680).length < 2 ^ (prefixWord ++ tailWord_838680).sum := by decide
  have hdescent : baseEnd_838680 < baseStart_838680 := by decide
  rcases family_descends (prefixWord ++ tailWord_838680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838687 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 3, 2, 2]
def baseStart_838687 : Nat := 118140960795 + 838687 * 2 ^ 59
def prefixEnd_838687 : Nat := 4983230072969 + 3 ^ 40 * 838687 * 2
def baseEnd_838687 : Nat := 430649549677465366955455

theorem tailTrace_838687 : CollatzResearch.WordTrace tailWord_838687 prefixEnd_838687 430649549677465366955455 := by
  unfold tailWord_838687
  simp only [CollatzResearch.WordTrace]
  refine ⟨30589427912587710181082315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20392951941725140120721543 30589427912587710181082315)
  ·
    refine ⟨45884141868881565271623473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30589427912587710181082315 45884141868881565271623473)
    ·
      refine ⟨34413106401661173953717605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45884141868881565271623473 34413106401661173953717605)
      ·
        refine ⟨6452457450311470116322051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34413106401661173953717605 6452457450311470116322051)
        ·
          refine ⟨9678686175467205174483077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6452457450311470116322051 9678686175467205174483077)
          ·
            refine ⟨1814753657900100970215577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9678686175467205174483077 1814753657900100970215577)
            ·
              refine ⟨1361065243425075727661683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1814753657900100970215577 1361065243425075727661683)
              ·
                refine ⟨2041597865137613591492525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361065243425075727661683 2041597865137613591492525)
                ·
                  refine ⟨765599199426605096809697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2041597865137613591492525 765599199426605096809697)
                  ·
                    refine ⟨574199399569953822607273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 765599199426605096809697 574199399569953822607273)
                    ·
                      refine ⟨430649549677465366955455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574199399569953822607273 430649549677465366955455)
                      ·
                        rfl

theorem cell23_838687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_838687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838687 prefixEnd_838687 := by exact prefixLift 838687
  have htrace : WordTrace (prefixWord ++ tailWord_838687) baseStart_838687 baseEnd_838687 := by
    simpa [prefixWord, tailWord_838687, baseEnd_838687] using wordTrace_append hprefix tailTrace_838687
  have hstable : (prefixWord ++ tailWord_838687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838687).length < 2 ^ (prefixWord ++ tailWord_838687).sum := by decide
  have hdescent : baseEnd_838687 < baseStart_838687 := by decide
  rcases family_descends (prefixWord ++ tailWord_838687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838710 : List Nat := [5, 1, 2, 1, 1, 2, 4, 7]
def baseStart_838710 : Nat := 118140960795 + 838710 * 2 ^ 59
def prefixEnd_838710 : Nat := 4983230072969 + 3 ^ 40 * 838710 * 2
def baseEnd_838710 : Nat := 15950420730834028776587

theorem tailTrace_838710 : CollatzResearch.WordTrace tailWord_838710 prefixEnd_838710 15950420730834028776587 := by
  unfold tailWord_838710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1911891674469024069323099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20393511194336256739446389 1911891674469024069323099)
  ·
    refine ⟨2867837511703536103984649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1911891674469024069323099 2867837511703536103984649)
    ·
      refine ⟨2150878133777652077988487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2867837511703536103984649 2150878133777652077988487)
      ·
        refine ⟨3226317200666478116982731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2150878133777652077988487 3226317200666478116982731)
        ·
          refine ⟨4839475800999717175474097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3226317200666478116982731 4839475800999717175474097)
          ·
            refine ⟨3629606850749787881605573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4839475800999717175474097 3629606850749787881605573)
            ·
              refine ⟨680551284515585227801045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3629606850749787881605573 680551284515585227801045)
              ·
                refine ⟨15950420730834028776587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 680551284515585227801045 15950420730834028776587)
                ·
                  rfl

theorem cell23_838710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_838710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838710 prefixEnd_838710 := by exact prefixLift 838710
  have htrace : WordTrace (prefixWord ++ tailWord_838710) baseStart_838710 baseEnd_838710 := by
    simpa [prefixWord, tailWord_838710, baseEnd_838710] using wordTrace_append hprefix tailTrace_838710
  have hstable : (prefixWord ++ tailWord_838710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838710).length < 2 ^ (prefixWord ++ tailWord_838710).sum := by decide
  have hdescent : baseEnd_838710 < baseStart_838710 := by decide
  rcases family_descends (prefixWord ++ tailWord_838710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838736 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 4, 6]
def baseStart_838736 : Nat := 118140960795 + 838736 * 2 ^ 59
def prefixEnd_838736 : Nat := 4983230072969 + 3 ^ 40 * 838736 * 2
def baseEnd_838736 : Nat := 143558236743178558414243

theorem tailTrace_838736 : CollatzResearch.WordTrace tailWord_838736 prefixEnd_838736 143558236743178558414243 := by
  unfold tailWord_838736
  simp only [CollatzResearch.WordTrace]
  refine ⟨15295607544705095774808031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20394143392940127699744041 15295607544705095774808031)
  ·
    refine ⟨22943411317057643662212047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15295607544705095774808031 22943411317057643662212047)
    ·
      refine ⟨34415116975586465493318071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22943411317057643662212047 34415116975586465493318071)
      ·
        refine ⟨51622675463379698239977107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34415116975586465493318071 51622675463379698239977107)
        ·
          refine ⟨77434013195069547359965661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51622675463379698239977107 77434013195069547359965661)
          ·
            refine ⟨29037754948151080259987123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77434013195069547359965661 29037754948151080259987123)
            ·
              refine ⟨43556632422226620389980685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29037754948151080259987123 43556632422226620389980685)
              ·
                refine ⟨16333737158334982646242757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43556632422226620389980685 16333737158334982646242757)
                ·
                  refine ⟨3062575717187809246170517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16333737158334982646242757 3062575717187809246170517)
                  ·
                    refine ⟨143558236743178558414243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3062575717187809246170517 143558236743178558414243)
                    ·
                      rfl

theorem cell23_838736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_838736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838736 prefixEnd_838736 := by exact prefixLift 838736
  have htrace : WordTrace (prefixWord ++ tailWord_838736) baseStart_838736 baseEnd_838736 := by
    simpa [prefixWord, tailWord_838736, baseEnd_838736] using wordTrace_append hprefix tailTrace_838736
  have hstable : (prefixWord ++ tailWord_838736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838736).length < 2 ^ (prefixWord ++ tailWord_838736).sum := by decide
  have hdescent : baseEnd_838736 < baseStart_838736 := by decide
  rcases family_descends (prefixWord ++ tailWord_838736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838754 : List Nat := [3, 3, 2, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_838754 : Nat := 118140960795 + 838754 * 2 ^ 59
def prefixEnd_838754 : Nat := 4983230072969 + 3 ^ 40 * 838754 * 2
def baseEnd_838754 : Nat := 430683952881316604817647

theorem tailTrace_838754 : CollatzResearch.WordTrace tailWord_838754 prefixEnd_838754 430683952881316604817647 := by
  unfold tailWord_838754
  simp only [CollatzResearch.WordTrace]
  refine ⟨7647967900836245155942829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20394581068896653749180877 7647967900836245155942829)
  ·
    refine ⟨2867987962813591933478561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7647967900836245155942829 2867987962813591933478561)
    ·
      refine ⟨2150990972110193950108921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2867987962813591933478561 2150990972110193950108921)
      ·
        refine ⟨1613243229082645462581691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2150990972110193950108921 1613243229082645462581691)
        ·
          refine ⟨2419864843623968193872537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613243229082645462581691 2419864843623968193872537)
          ·
            refine ⟨1814898632717976145404403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2419864843623968193872537 1814898632717976145404403)
            ·
              refine ⟨2722347949076964218106605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814898632717976145404403 2722347949076964218106605)
              ·
                refine ⟨1020880480903861581789977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2722347949076964218106605 1020880480903861581789977)
                ·
                  refine ⟨765660360677896186342483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1020880480903861581789977 765660360677896186342483)
                  ·
                    refine ⟨1148490541016844279513725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 765660360677896186342483 1148490541016844279513725)
                    ·
                      refine ⟨430683952881316604817647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1148490541016844279513725 430683952881316604817647)
                      ·
                        rfl

theorem cell23_838754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_838754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838754 prefixEnd_838754 := by exact prefixLift 838754
  have htrace : WordTrace (prefixWord ++ tailWord_838754) baseStart_838754 baseEnd_838754 := by
    simpa [prefixWord, tailWord_838754, baseEnd_838754] using wordTrace_append hprefix tailTrace_838754
  have hstable : (prefixWord ++ tailWord_838754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838754).length < 2 ^ (prefixWord ++ tailWord_838754).sum := by decide
  have hdescent : baseEnd_838754 < baseStart_838754 := by decide
  rcases family_descends (prefixWord ++ tailWord_838754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838777 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 1, 4, 2]
def baseStart_838777 : Nat := 118140960795 + 838777 * 2 ^ 59
def prefixEnd_838777 : Nat := 4983230072969 + 3 ^ 40 * 838777 * 2
def baseEnd_838777 : Nat := 430695762936370014830041

theorem tailTrace_838777 : CollatzResearch.WordTrace tailWord_838777 prefixEnd_838777 430695762936370014830041 := by
  unfold tailWord_838777
  simp only [CollatzResearch.WordTrace]
  refine ⟨30592710482261655551858585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20395140321507770367905723 30592710482261655551858585)
  ·
    refine ⟨22944532861696241663893939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30592710482261655551858585 22944532861696241663893939)
    ·
      refine ⟨34416799292544362495840909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22944532861696241663893939 34416799292544362495840909)
      ·
        refine ⟨12906299734704135935940341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34416799292544362495840909 12906299734704135935940341)
        ·
          refine ⟨1209965600128512743994407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12906299734704135935940341 1209965600128512743994407)
          ·
            refine ⟨1814948400192769115991611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209965600128512743994407 1814948400192769115991611)
            ·
              refine ⟨2722422600289153673987417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814948400192769115991611 2722422600289153673987417)
              ·
                refine ⟨2041816950216865255490563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2722422600289153673987417 2041816950216865255490563)
                ·
                  refine ⟨3062725425325297883235845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2041816950216865255490563 3062725425325297883235845)
                  ·
                    refine ⟨574261017248493353106721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3062725425325297883235845 574261017248493353106721)
                    ·
                      refine ⟨430695762936370014830041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574261017248493353106721 430695762936370014830041)
                      ·
                        rfl

theorem cell23_838777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_838777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838777 prefixEnd_838777 := by exact prefixLift 838777
  have htrace : WordTrace (prefixWord ++ tailWord_838777) baseStart_838777 baseEnd_838777 := by
    simpa [prefixWord, tailWord_838777, baseEnd_838777] using wordTrace_append hprefix tailTrace_838777
  have hstable : (prefixWord ++ tailWord_838777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838777).length < 2 ^ (prefixWord ++ tailWord_838777).sum := by decide
  have hdescent : baseEnd_838777 < baseStart_838777 := by decide
  rcases family_descends (prefixWord ++ tailWord_838777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838794 : List Nat := [3, 1, 2, 3, 1, 1, 4, 2, 2, 2, 2]
def baseStart_838794 : Nat := 118140960795 + 838794 * 2 ^ 59
def prefixEnd_838794 : Nat := 4983230072969 + 3 ^ 40 * 838794 * 2
def baseEnd_838794 : Nat := 430704492107496448317463

theorem tailTrace_838794 : CollatzResearch.WordTrace tailWord_838794 prefixEnd_838794 430704492107496448317463 := by
  unfold tailWord_838794
  simp only [CollatzResearch.WordTrace]
  refine ⟨7648332630800016863806859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20395553682133378303484957 7648332630800016863806859)
  ·
    refine ⟨11472498946200025295710289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7648332630800016863806859 11472498946200025295710289)
    ·
      refine ⟨8604374209650018971782717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11472498946200025295710289 8604374209650018971782717)
      ·
        refine ⟨3226640328618757114418519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8604374209650018971782717 3226640328618757114418519)
        ·
          refine ⟨4839960492928135671627779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3226640328618757114418519 4839960492928135671627779)
          ·
            refine ⟨7259940739392203507441669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4839960492928135671627779 7259940739392203507441669)
            ·
              refine ⟨1361238888636038157645313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7259940739392203507441669 1361238888636038157645313)
              ·
                refine ⟨1020929166477028618233985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361238888636038157645313 1020929166477028618233985)
                ·
                  refine ⟨765696874857771463675489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1020929166477028618233985 765696874857771463675489)
                  ·
                    refine ⟨574272656143328597756617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 765696874857771463675489 574272656143328597756617)
                    ·
                      refine ⟨430704492107496448317463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574272656143328597756617 430704492107496448317463)
                      ·
                        rfl

theorem cell23_838794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_838794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838794 prefixEnd_838794 := by exact prefixLift 838794
  have htrace : WordTrace (prefixWord ++ tailWord_838794) baseStart_838794 baseEnd_838794 := by
    simpa [prefixWord, tailWord_838794, baseEnd_838794] using wordTrace_append hprefix tailTrace_838794
  have hstable : (prefixWord ++ tailWord_838794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838794).length < 2 ^ (prefixWord ++ tailWord_838794).sum := by decide
  have hdescent : baseEnd_838794 < baseStart_838794 := by decide
  rcases family_descends (prefixWord ++ tailWord_838794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838810 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3]
def baseStart_838810 : Nat := 118140960795 + 838810 * 2 ^ 59
def prefixEnd_838810 : Nat := 4983230072969 + 3 ^ 40 * 838810 * 2
def baseEnd_838810 : Nat := 430712707797968385717389

theorem tailTrace_838810 : CollatzResearch.WordTrace tailWord_838810 prefixEnd_838810 430712707797968385717389 := by
  unfold tailWord_838810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7648478522785525546952471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20395942727428068125206589 7648478522785525546952471)
  ·
    refine ⟨11472717784178288320428707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7648478522785525546952471 11472717784178288320428707)
    ·
      refine ⟨17209076676267432480643061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11472717784178288320428707 17209076676267432480643061)
      ·
        refine ⟨1613350938400071795060287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17209076676267432480643061 1613350938400071795060287)
        ·
          refine ⟨2420026407600107692590431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613350938400071795060287 2420026407600107692590431)
          ·
            refine ⟨3630039611400161538885647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420026407600107692590431 3630039611400161538885647)
            ·
              refine ⟨5445059417100242308328471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3630039611400161538885647 5445059417100242308328471)
              ·
                refine ⟨8167589125650363462492707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5445059417100242308328471 8167589125650363462492707)
                ·
                  refine ⟨12251383688475545193739061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8167589125650363462492707 12251383688475545193739061)
                  ·
                    refine ⟨1148567220794582361913037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12251383688475545193739061 1148567220794582361913037)
                    ·
                      refine ⟨430712707797968385717389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1148567220794582361913037 430712707797968385717389)
                      ·
                        rfl

theorem cell23_838810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_838810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838810 prefixEnd_838810 := by exact prefixLift 838810
  have htrace : WordTrace (prefixWord ++ tailWord_838810) baseStart_838810 baseEnd_838810 := by
    simpa [prefixWord, tailWord_838810, baseEnd_838810] using wordTrace_append hprefix tailTrace_838810
  have hstable : (prefixWord ++ tailWord_838810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838810).length < 2 ^ (prefixWord ++ tailWord_838810).sum := by decide
  have hdescent : baseEnd_838810 < baseStart_838810 := by decide
  rcases family_descends (prefixWord ++ tailWord_838810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838813 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_838813 : Nat := 118140960795 + 838813 * 2 ^ 59
def prefixEnd_838813 : Nat := 4983230072969 + 3 ^ 40 * 838813 * 2
def baseEnd_838813 : Nat := 143571416079977291326625

theorem tailTrace_838813 : CollatzResearch.WordTrace tailWord_838813 prefixEnd_838813 143571416079977291326625 := by
  unfold tailWord_838813
  simp only [CollatzResearch.WordTrace]
  refine ⟨30594023510131233700169093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20396015673420822466779395 30594023510131233700169093)
  ·
    refine ⟨5736379408149606318781705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30594023510131233700169093 5736379408149606318781705)
    ·
      refine ⟨4302284556112204739086279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5736379408149606318781705 4302284556112204739086279)
      ·
        refine ⟨6453426834168307108629419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4302284556112204739086279 6453426834168307108629419)
        ·
          refine ⟨9680140251252460662944129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6453426834168307108629419 9680140251252460662944129)
          ·
            refine ⟨7260105188439345497208097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9680140251252460662944129 7260105188439345497208097)
            ·
              refine ⟨5445078891329509122906073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7260105188439345497208097 5445078891329509122906073)
              ·
                refine ⟨4083809168497131842179555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5445078891329509122906073 4083809168497131842179555)
                ·
                  refine ⟨6125713752745697763269333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4083809168497131842179555 6125713752745697763269333)
                  ·
                    refine ⟨143571416079977291326625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6125713752745697763269333 143571416079977291326625)
                    ·
                      rfl

theorem cell23_838813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_838813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838813 prefixEnd_838813 := by exact prefixLift 838813
  have htrace : WordTrace (prefixWord ++ tailWord_838813) baseStart_838813 baseEnd_838813 := by
    simpa [prefixWord, tailWord_838813, baseEnd_838813] using wordTrace_append hprefix tailTrace_838813
  have hstable : (prefixWord ++ tailWord_838813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838813).length < 2 ^ (prefixWord ++ tailWord_838813).sum := by decide
  have hdescent : baseEnd_838813 < baseStart_838813 := by decide
  rcases family_descends (prefixWord ++ tailWord_838813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838894 : List Nat := [4, 1, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_838894 : Nat := 118140960795 + 838894 * 2 ^ 59
def prefixEnd_838894 : Nat := 4983230072969 + 3 ^ 40 * 838894 * 2
def baseEnd_838894 : Nat := 143585280057648685689001

theorem tailTrace_838894 : CollatzResearch.WordTrace tailWord_838894 prefixEnd_838894 143585280057648685689001 := by
  unfold tailWord_838894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824622227854723066733467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20397985215225189689245157 3824622227854723066733467)
  ·
    refine ⟨5736933341782084600100201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3824622227854723066733467 5736933341782084600100201)
    ·
      refine ⟨4302700006336563450075151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5736933341782084600100201 4302700006336563450075151)
      ·
        refine ⟨6454050009504845175112727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4302700006336563450075151 6454050009504845175112727)
        ·
          refine ⟨9681075014257267762669091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6454050009504845175112727 9681075014257267762669091)
          ·
            refine ⟨14521612521385901644003637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9681075014257267762669091 14521612521385901644003637)
            ·
              refine ⟨1361401173879928279125341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14521612521385901644003637 1361401173879928279125341)
              ·
                refine ⟨510525440204973104672003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1361401173879928279125341 510525440204973104672003)
                ·
                  refine ⟨765788160307459657008005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510525440204973104672003 765788160307459657008005)
                  ·
                    refine ⟨143585280057648685689001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 765788160307459657008005 143585280057648685689001)
                    ·
                      rfl

theorem cell23_838894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_838894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838894 prefixEnd_838894 := by exact prefixLift 838894
  have htrace : WordTrace (prefixWord ++ tailWord_838894) baseStart_838894 baseEnd_838894 := by
    simpa [prefixWord, tailWord_838894, baseEnd_838894] using wordTrace_append hprefix tailTrace_838894
  have hstable : (prefixWord ++ tailWord_838894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838894).length < 2 ^ (prefixWord ++ tailWord_838894).sum := by decide
  have hdescent : baseEnd_838894 < baseStart_838894 := by decide
  rcases family_descends (prefixWord ++ tailWord_838894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838963 : List Nat := [1, 1, 1, 2, 5, 13]
def baseStart_838963 : Nat := 118140960795 + 838963 * 2 ^ 59
def prefixEnd_838963 : Nat := 4983230072969 + 3 ^ 40 * 838963 * 2
def baseEnd_838963 : Nat := 1772803581638297477795

theorem tailTrace_838963 : CollatzResearch.WordTrace tailWord_838963 prefixEnd_838963 1772803581638297477795 := by
  unfold tailWord_838963
  simp only [CollatzResearch.WordTrace]
  refine ⟨30599494459587809318129543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20399662973058539545419695 30599494459587809318129543)
  ·
    refine ⟨45899241689381713977194315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30599494459587809318129543 45899241689381713977194315)
    ·
      refine ⟨68848862534072570965791473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45899241689381713977194315 68848862534072570965791473)
      ·
        refine ⟨51636646900554428224343605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68848862534072570965791473 51636646900554428224343605)
        ·
          refine ⟨4840935646926977646032213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51636646900554428224343605 4840935646926977646032213)
          ·
            refine ⟨1772803581638297477795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 4840935646926977646032213 1772803581638297477795)
            ·
              rfl

theorem cell23_838963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 13].length) (baseStart_838963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838963 prefixEnd_838963 := by exact prefixLift 838963
  have htrace : WordTrace (prefixWord ++ tailWord_838963) baseStart_838963 baseEnd_838963 := by
    simpa [prefixWord, tailWord_838963, baseEnd_838963] using wordTrace_append hprefix tailTrace_838963
  have hstable : (prefixWord ++ tailWord_838963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838963).length < 2 ^ (prefixWord ++ tailWord_838963).sum := by decide
  have hdescent : baseEnd_838963 < baseStart_838963 := by decide
  rcases family_descends (prefixWord ++ tailWord_838963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838970 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_838970 : Nat := 118140960795 + 838970 * 2 ^ 59
def prefixEnd_838970 : Nat := 4983230072969 + 3 ^ 40 * 838970 * 2
def baseEnd_838970 : Nat := 430794864702687759716653

theorem tailTrace_838970 : CollatzResearch.WordTrace tailWord_838970 prefixEnd_838970 430794864702687759716653 := by
  unfold tailWord_838970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7649937442640612378408591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20399833180374966342422909 7649937442640612378408591)
  ·
    refine ⟨11474906163960918567612887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7649937442640612378408591 11474906163960918567612887)
    ·
      refine ⟨17212359245941377851419331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11474906163960918567612887 17212359245941377851419331)
      ·
        refine ⟨25818538868912066777128997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17212359245941377851419331 25818538868912066777128997)
        ·
          refine ⟨4840976037921012520711687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25818538868912066777128997 4840976037921012520711687)
          ·
            refine ⟨7261464056881518781067531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4840976037921012520711687 7261464056881518781067531)
            ·
              refine ⟨10892196085322278171601297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7261464056881518781067531 10892196085322278171601297)
              ·
                refine ⟨8169147063991708628700973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10892196085322278171601297 8169147063991708628700973)
                ·
                  refine ⟨3063430148996890735762865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8169147063991708628700973 3063430148996890735762865)
                  ·
                    refine ⟨2297572611747668051822149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3063430148996890735762865 2297572611747668051822149)
                    ·
                      refine ⟨430794864702687759716653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2297572611747668051822149 430794864702687759716653)
                      ·
                        rfl

theorem cell23_838970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_838970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838970 prefixEnd_838970 := by exact prefixLift 838970
  have htrace : WordTrace (prefixWord ++ tailWord_838970) baseStart_838970 baseEnd_838970 := by
    simpa [prefixWord, tailWord_838970, baseEnd_838970] using wordTrace_append hprefix tailTrace_838970
  have hstable : (prefixWord ++ tailWord_838970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838970).length < 2 ^ (prefixWord ++ tailWord_838970).sum := by decide
  have hdescent : baseEnd_838970 < baseStart_838970 := by decide
  rcases family_descends (prefixWord ++ tailWord_838970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_838997 : List Nat := [1, 3, 2, 2, 3, 2, 3, 7]
def baseStart_838997 : Nat := 118140960795 + 838997 * 2 ^ 59
def prefixEnd_838997 : Nat := 4983230072969 + 3 ^ 40 * 838997 * 2
def baseEnd_838997 : Nat := 15955878840013302002927

theorem tailTrace_838997 : CollatzResearch.WordTrace tailWord_838997 prefixEnd_838997 15955878840013302002927 := by
  unfold tailWord_838997
  simp only [CollatzResearch.WordTrace]
  refine ⟨30600734541464633124867245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20400489694309755416578163 30600734541464633124867245)
  ·
    refine ⟨11475275453049237421825217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30600734541464633124867245 11475275453049237421825217)
    ·
      refine ⟨8606456589786928066368913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11475275453049237421825217 8606456589786928066368913)
      ·
        refine ⟨6454842442340196049776685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8606456589786928066368913 6454842442340196049776685)
        ·
          refine ⟨2420565915877573518666257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6454842442340196049776685 2420565915877573518666257)
          ·
            refine ⟨1815424436908180138999693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2420565915877573518666257 1815424436908180138999693)
            ·
              refine ⟨680784163840567552124885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1815424436908180138999693 680784163840567552124885)
              ·
                refine ⟨15955878840013302002927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 680784163840567552124885 15955878840013302002927)
                ·
                  rfl

theorem cell23_838997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 3, 7].length) (baseStart_838997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_838997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_838997 prefixEnd_838997 := by exact prefixLift 838997
  have htrace : WordTrace (prefixWord ++ tailWord_838997) baseStart_838997 baseEnd_838997 := by
    simpa [prefixWord, tailWord_838997, baseEnd_838997] using wordTrace_append hprefix tailTrace_838997
  have hstable : (prefixWord ++ tailWord_838997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_838997).length < 2 ^ (prefixWord ++ tailWord_838997).sum := by decide
  have hdescent : baseEnd_838997 < baseStart_838997 := by decide
  rcases family_descends (prefixWord ++ tailWord_838997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839005 : List Nat := [1, 4, 5, 1, 1, 2, 2, 1, 1, 5]
def baseStart_839005 : Nat := 118140960795 + 839005 * 2 ^ 59
def prefixEnd_839005 : Nat := 4983230072969 + 3 ^ 40 * 839005 * 2
def baseEnd_839005 : Nat := 143604278841865040926331

theorem tailTrace_839005 : CollatzResearch.WordTrace tailWord_839005 prefixEnd_839005 143604278841865040926331 := by
  unfold tailWord_839005
  simp only [CollatzResearch.WordTrace]
  refine ⟨30601026325435650491158469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20400684216957100327438979 30601026325435650491158469)
  ·
    refine ⟨5737692436019184467092213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30601026325435650491158469 5737692436019184467092213)
    ·
      refine ⟨537908665876798543789895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5737692436019184467092213 537908665876798543789895)
      ·
        refine ⟨806862998815197815684843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537908665876798543789895 806862998815197815684843)
        ·
          refine ⟨1210294498222796723527265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806862998815197815684843 1210294498222796723527265)
          ·
            refine ⟨907720873667097542645449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1210294498222796723527265 907720873667097542645449)
            ·
              refine ⟨680790655250323156984087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 907720873667097542645449 680790655250323156984087)
              ·
                refine ⟨1021185982875484735476131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680790655250323156984087 1021185982875484735476131)
                ·
                  refine ⟨1531778974313227103214197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021185982875484735476131 1531778974313227103214197)
                  ·
                    refine ⟨143604278841865040926331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1531778974313227103214197 143604278841865040926331)
                    ·
                      rfl

theorem cell23_839005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_839005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839005 prefixEnd_839005 := by exact prefixLift 839005
  have htrace : WordTrace (prefixWord ++ tailWord_839005) baseStart_839005 baseEnd_839005 := by
    simpa [prefixWord, tailWord_839005, baseEnd_839005] using wordTrace_append hprefix tailTrace_839005
  have hstable : (prefixWord ++ tailWord_839005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839005).length < 2 ^ (prefixWord ++ tailWord_839005).sum := by decide
  have hdescent : baseEnd_839005 < baseStart_839005 := by decide
  rcases family_descends (prefixWord ++ tailWord_839005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839007 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 4, 1, 3]
def baseStart_839007 : Nat := 118140960795 + 839007 * 2 ^ 59
def prefixEnd_839007 : Nat := 4983230072969 + 3 ^ 40 * 839007 * 2
def baseEnd_839007 : Nat := 430813863486904114953983

theorem tailTrace_839007 : CollatzResearch.WordTrace tailWord_839007 prefixEnd_839007 430813863486904114953983 := by
  unfold tailWord_839007
  simp only [CollatzResearch.WordTrace]
  refine ⟨30601099271428404832731275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20400732847618936555154183 30601099271428404832731275)
  ·
    refine ⟨45901648907142607249096913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30601099271428404832731275 45901648907142607249096913)
    ·
      refine ⟨34426236680356955436822685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45901648907142607249096913 34426236680356955436822685)
      ·
        refine ⟨12909838755133858288808507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34426236680356955436822685 12909838755133858288808507)
        ·
          refine ⟨19364758132700787433212761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12909838755133858288808507 19364758132700787433212761)
          ·
            refine ⟨14523568599525590574909571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19364758132700787433212761 14523568599525590574909571)
            ·
              refine ⟨21785352899288385862364357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14523568599525590574909571 21785352899288385862364357)
              ·
                refine ⟨4084753668616572349193317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21785352899288385862364357 4084753668616572349193317)
                ·
                  refine ⟨765891312865607315473747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4084753668616572349193317 765891312865607315473747)
                  ·
                    refine ⟨1148836969298410973210621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 765891312865607315473747 1148836969298410973210621)
                    ·
                      refine ⟨430813863486904114953983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1148836969298410973210621 430813863486904114953983)
                      ·
                        rfl

theorem cell23_839007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_839007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839007 prefixEnd_839007 := by exact prefixLift 839007
  have htrace : WordTrace (prefixWord ++ tailWord_839007) baseStart_839007 baseEnd_839007 := by
    simpa [prefixWord, tailWord_839007, baseEnd_839007] using wordTrace_append hprefix tailTrace_839007
  have hstable : (prefixWord ++ tailWord_839007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839007).length < 2 ^ (prefixWord ++ tailWord_839007).sum := by decide
  have hdescent : baseEnd_839007 < baseStart_839007 := by decide
  rcases family_descends (prefixWord ++ tailWord_839007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839008 : List Nat := [2, 1, 1, 3, 4, 2, 2, 3, 1, 2, 2]
def baseStart_839008 : Nat := 118140960795 + 839008 * 2 ^ 59
def prefixEnd_839008 : Nat := 4983230072969 + 3 ^ 40 * 839008 * 2
def baseEnd_839008 : Nat := 430814376967558611041479

theorem tailTrace_839008 : CollatzResearch.WordTrace tailWord_839008 prefixEnd_839008 430814376967558611041479 := by
  unfold tailWord_839008
  simp only [CollatzResearch.WordTrace]
  refine ⟨15300567872212391001758839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20400757162949854669011785 15300567872212391001758839)
  ·
    refine ⟨22950851808318586502638259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15300567872212391001758839 22950851808318586502638259)
    ·
      refine ⟨34426277712477879753957389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22950851808318586502638259 34426277712477879753957389)
      ·
        refine ⟨12909854142179204907734021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34426277712477879753957389 12909854142179204907734021)
        ·
          refine ⟨2420597651658600920200129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12909854142179204907734021 2420597651658600920200129)
          ·
            refine ⟨1815448238743950690150097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2420597651658600920200129 1815448238743950690150097)
            ·
              refine ⟨1361586179057963017612573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1815448238743950690150097 1361586179057963017612573)
              ·
                refine ⟨510594817146736131604715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1361586179057963017612573 510594817146736131604715)
                ·
                  refine ⟨765892225720104197407073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510594817146736131604715 765892225720104197407073)
                  ·
                    refine ⟨574419169290078148055305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 765892225720104197407073 574419169290078148055305)
                    ·
                      refine ⟨430814376967558611041479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574419169290078148055305 430814376967558611041479)
                      ·
                        rfl

theorem cell23_839008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_839008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839008 prefixEnd_839008 := by exact prefixLift 839008
  have htrace : WordTrace (prefixWord ++ tailWord_839008) baseStart_839008 baseEnd_839008 := by
    simpa [prefixWord, tailWord_839008, baseEnd_839008] using wordTrace_append hprefix tailTrace_839008
  have hstable : (prefixWord ++ tailWord_839008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839008).length < 2 ^ (prefixWord ++ tailWord_839008).sum := by decide
  have hdescent : baseEnd_839008 < baseStart_839008 := by decide
  rcases family_descends (prefixWord ++ tailWord_839008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839011 : List Nat := [1, 1, 1, 5, 2, 4, 2, 1, 1, 2, 3]
def baseStart_839011 : Nat := 118140960795 + 839011 * 2 ^ 59
def prefixEnd_839011 : Nat := 4983230072969 + 3 ^ 40 * 839011 * 2
def baseEnd_839011 : Nat := 430815917409522099303965

theorem tailTrace_839011 : CollatzResearch.WordTrace tailWord_839011 prefixEnd_839011 430815917409522099303965 := by
  unfold tailWord_839011
  simp only [CollatzResearch.WordTrace]
  refine ⟨30601245163413913515876887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20400830108942609010584591 30601245163413913515876887)
  ·
    refine ⟨45901867745120870273815331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30601245163413913515876887 45901867745120870273815331)
    ·
      refine ⟨68852801617681305410722997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45901867745120870273815331 68852801617681305410722997)
      ·
        refine ⟨6454950151657622382255281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68852801617681305410722997 6454950151657622382255281)
        ·
          refine ⟨4841212613743216786691461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6454950151657622382255281 4841212613743216786691461)
          ·
            refine ⟨907727365076853147504649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4841212613743216786691461 907727365076853147504649)
            ·
              refine ⟨680795523807639860628487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 907727365076853147504649 680795523807639860628487)
              ·
                refine ⟨1021193285711459790942731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680795523807639860628487 1021193285711459790942731)
                ·
                  refine ⟨1531789928567189686414097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021193285711459790942731 1531789928567189686414097)
                  ·
                    refine ⟨1148842446425392264810573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1531789928567189686414097 1148842446425392264810573)
                    ·
                      refine ⟨430815917409522099303965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1148842446425392264810573 430815917409522099303965)
                      ·
                        rfl

theorem cell23_839011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_839011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839011 prefixEnd_839011 := by exact prefixLift 839011
  have htrace : WordTrace (prefixWord ++ tailWord_839011) baseStart_839011 baseEnd_839011 := by
    simpa [prefixWord, tailWord_839011, baseEnd_839011] using wordTrace_append hprefix tailTrace_839011
  have hstable : (prefixWord ++ tailWord_839011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839011).length < 2 ^ (prefixWord ++ tailWord_839011).sum := by decide
  have hdescent : baseEnd_839011 < baseStart_839011 := by decide
  rcases family_descends (prefixWord ++ tailWord_839011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839017 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 5, 3, 2]
def baseStart_839017 : Nat := 118140960795 + 839017 * 2 ^ 59
def prefixEnd_839017 : Nat := 4983230072969 + 3 ^ 40 * 839017 * 2
def baseEnd_839017 : Nat := 430818998293449075828937

theorem tailTrace_839017 : CollatzResearch.WordTrace tailWord_839017 prefixEnd_839017 430818998293449075828937 := by
  unfold tailWord_839017
  simp only [CollatzResearch.WordTrace]
  refine ⟨30601464001392176540595305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20400976000928117693730203 30601464001392176540595305)
  ·
    refine ⟨22951098001044132405446479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30601464001392176540595305 22951098001044132405446479)
    ·
      refine ⟨34426647001566198608169719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22951098001044132405446479 34426647001566198608169719)
      ·
        refine ⟨51639970502349297912254579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34426647001566198608169719 51639970502349297912254579)
        ·
          refine ⟨77459955753523946868381869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51639970502349297912254579 77459955753523946868381869)
          ·
            refine ⟨29047483407571480075643201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77459955753523946868381869 29047483407571480075643201)
            ·
              refine ⟨21785612555678610056732401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29047483407571480075643201 21785612555678610056732401)
              ·
                refine ⟨16339209416758957542549301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21785612555678610056732401 16339209416758957542549301)
                ·
                  refine ⟨1531800882821152269613997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16339209416758957542549301 1531800882821152269613997)
                  ·
                    refine ⟨574425331057932101105249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1531800882821152269613997 574425331057932101105249)
                    ·
                      refine ⟨430818998293449075828937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 574425331057932101105249 430818998293449075828937)
                      ·
                        rfl

theorem cell23_839017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 3, 2].length) (baseStart_839017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839017 prefixEnd_839017 := by exact prefixLift 839017
  have htrace : WordTrace (prefixWord ++ tailWord_839017) baseStart_839017 baseEnd_839017 := by
    simpa [prefixWord, tailWord_839017, baseEnd_839017] using wordTrace_append hprefix tailTrace_839017
  have hstable : (prefixWord ++ tailWord_839017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839017).length < 2 ^ (prefixWord ++ tailWord_839017).sum := by decide
  have hdescent : baseEnd_839017 < baseStart_839017 := by decide
  rcases family_descends (prefixWord ++ tailWord_839017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839018 : List Nat := [3, 1, 3, 3, 3, 1, 1, 2, 2, 4]
def baseStart_839018 : Nat := 118140960795 + 839018 * 2 ^ 59
def prefixEnd_839018 : Nat := 4983230072969 + 3 ^ 40 * 839018 * 2
def baseEnd_839018 : Nat := 143606503924701190638811

theorem tailTrace_839018 : CollatzResearch.WordTrace tailWord_839018 prefixEnd_839018 143606503924701190638811 := by
  unfold tailWord_839018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7650375118597138427845427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20401000316259035807587805 7650375118597138427845427)
  ·
    refine ⟨11475562677895707641768141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7650375118597138427845427 11475562677895707641768141)
    ·
      refine ⟨4303336004210890365663053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11475562677895707641768141 4303336004210890365663053)
      ·
        refine ⟨1613751001579083887123645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4303336004210890365663053 1613751001579083887123645)
        ·
          refine ⟨605156625592156457671367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1613751001579083887123645 605156625592156457671367)
          ·
            refine ⟨907734938388234686507051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605156625592156457671367 907734938388234686507051)
            ·
              refine ⟨1361602407582352029760577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907734938388234686507051 1361602407582352029760577)
              ·
                refine ⟨1021201805686764022320433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1361602407582352029760577 1021201805686764022320433)
                ·
                  refine ⟨765901354265073016740325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1021201805686764022320433 765901354265073016740325)
                  ·
                    refine ⟨143606503924701190638811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 765901354265073016740325 143606503924701190638811)
                    ·
                      rfl

theorem cell23_839018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_839018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839018 prefixEnd_839018 := by exact prefixLift 839018
  have htrace : WordTrace (prefixWord ++ tailWord_839018) baseStart_839018 baseEnd_839018 := by
    simpa [prefixWord, tailWord_839018, baseEnd_839018] using wordTrace_append hprefix tailTrace_839018
  have hstable : (prefixWord ++ tailWord_839018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839018).length < 2 ^ (prefixWord ++ tailWord_839018).sum := by decide
  have hdescent : baseEnd_839018 < baseStart_839018 := by decide
  rcases family_descends (prefixWord ++ tailWord_839018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839038 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_839038 : Nat := 118140960795 + 839038 * 2 ^ 59
def prefixEnd_839038 : Nat := 4983230072969 + 3 ^ 40 * 839038 * 2
def baseEnd_839038 : Nat := 430829781387193493666341

theorem tailTrace_839038 : CollatzResearch.WordTrace tailWord_839038 prefixEnd_839038 430829781387193493666341 := by
  unfold tailWord_839038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3825278741789512140888721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20401486622877398084739845 3825278741789512140888721)
  ·
    refine ⟨2868959056342134105666541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3825278741789512140888721 2868959056342134105666541)
    ·
      refine ⟨1075859646128300289624953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2868959056342134105666541 1075859646128300289624953)
      ·
        refine ⟨806894734596225217218715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1075859646128300289624953 806894734596225217218715)
        ·
          refine ⟨1210342101894337825828073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806894734596225217218715 1210342101894337825828073)
          ·
            refine ⟨907756576420753369371055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1210342101894337825828073 907756576420753369371055)
            ·
              refine ⟨1361634864631130054056583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907756576420753369371055 1361634864631130054056583)
              ·
                refine ⟨2042452296946695081084875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361634864631130054056583 2042452296946695081084875)
                ·
                  refine ⟨3063678445420042621627313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042452296946695081084875 3063678445420042621627313)
                  ·
                    refine ⟨2297758834065031966220485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3063678445420042621627313 2297758834065031966220485)
                    ·
                      refine ⟨430829781387193493666341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2297758834065031966220485 430829781387193493666341)
                      ·
                        rfl

theorem cell23_839038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_839038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839038 prefixEnd_839038 := by exact prefixLift 839038
  have htrace : WordTrace (prefixWord ++ tailWord_839038) baseStart_839038 baseEnd_839038 := by
    simpa [prefixWord, tailWord_839038, baseEnd_839038] using wordTrace_append hprefix tailTrace_839038
  have hstable : (prefixWord ++ tailWord_839038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839038).length < 2 ^ (prefixWord ++ tailWord_839038).sum := by decide
  have hdescent : baseEnd_839038 < baseStart_839038 := by decide
  rcases family_descends (prefixWord ++ tailWord_839038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_839041 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_839041 : Nat := 118140960795 + 839041 * 2 ^ 59
def prefixEnd_839041 : Nat := 4983230072969 + 3 ^ 40 * 839041 * 2
def baseEnd_839041 : Nat := 430831321829156981928827

theorem tailTrace_839041 : CollatzResearch.WordTrace tailWord_839041 prefixEnd_839041 430831321829156981928827 := by
  unfold tailWord_839041
  simp only [CollatzResearch.WordTrace]
  refine ⟨30602339353305228639468977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20401559568870152426312651 30602339353305228639468977)
  ·
    refine ⟨22951754514978921479601733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30602339353305228639468977 22951754514978921479601733)
    ·
      refine ⟨4303453971558547777425325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22951754514978921479601733 4303453971558547777425325)
      ·
        refine ⟨1613795239334455416534497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4303453971558547777425325 1613795239334455416534497)
        ·
          refine ⟨1210346429500841562400873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1613795239334455416534497 1210346429500841562400873)
          ·
            refine ⟨907759822125631171800655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1210346429500841562400873 907759822125631171800655)
            ·
              refine ⟨1361639733188446757700983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907759822125631171800655 1361639733188446757700983)
              ·
                refine ⟨2042459599782670136551475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361639733188446757700983 2042459599782670136551475)
                ·
                  refine ⟨3063689399674005204827213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042459599782670136551475 3063689399674005204827213)
                  ·
                    refine ⟨1148883524877751951810205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3063689399674005204827213 1148883524877751951810205)
                    ·
                      refine ⟨430831321829156981928827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1148883524877751951810205 430831321829156981928827)
                      ·
                        rfl

theorem cell23_839041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_839041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_839041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_839041 prefixEnd_839041 := by exact prefixLift 839041
  have htrace : WordTrace (prefixWord ++ tailWord_839041) baseStart_839041 baseEnd_839041 := by
    simpa [prefixWord, tailWord_839041, baseEnd_839041] using wordTrace_append hprefix tailTrace_839041
  have hstable : (prefixWord ++ tailWord_839041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_839041).length < 2 ^ (prefixWord ++ tailWord_839041).sum := by decide
  have hdescent : baseEnd_839041 < baseStart_839041 := by decide
  rcases family_descends (prefixWord ++ tailWord_839041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
