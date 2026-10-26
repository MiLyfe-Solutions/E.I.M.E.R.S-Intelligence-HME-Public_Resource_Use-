import V185TrunkScan23Chunk0615

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3643012 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_3643012 : Nat := 118140960795 + 3643012 * 2 ^ 59
def prefixEnd_3643012 : Nat := 4983230072969 + 3 ^ 40 * 3643012 * 2
def baseEnd_3643012 : Nat := 1870616186097205932496099

theorem tailTrace_3643012 : CollatzResearch.WordTrace tailWord_3643012 prefixEnd_3643012 1870616186097205932496099 := by
  unfold tailWord_3643012
  simp only [CollatzResearch.WordTrace]
  refine ⟨66435781738998587880337645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88581042318664783840450193 66435781738998587880337645)
  ·
    refine ⟨24913418152124470455126617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66435781738998587880337645 24913418152124470455126617)
    ·
      refine ⟨18685063614093352841344963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24913418152124470455126617 18685063614093352841344963)
      ·
        refine ⟨28027595421140029262017445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18685063614093352841344963 28027595421140029262017445)
        ·
          refine ⟨5255174141463755486628271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28027595421140029262017445 5255174141463755486628271)
          ·
            refine ⟨7882761212195633229942407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5255174141463755486628271 7882761212195633229942407)
            ·
              refine ⟨11824141818293449844913611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7882761212195633229942407 11824141818293449844913611)
              ·
                refine ⟨17736212727440174767370417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11824141818293449844913611 17736212727440174767370417)
                ·
                  refine ⟨13302159545580131075527813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17736212727440174767370417 13302159545580131075527813)
                  ·
                    refine ⟨2494154914796274576661465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13302159545580131075527813 2494154914796274576661465)
                    ·
                      refine ⟨1870616186097205932496099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494154914796274576661465 1870616186097205932496099)
                      ·
                        rfl

theorem cell23_3643012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_3643012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643012 prefixEnd_3643012 := by exact prefixLift 3643012
  have htrace : WordTrace (prefixWord ++ tailWord_3643012) baseStart_3643012 baseEnd_3643012 := by
    simpa [prefixWord, tailWord_3643012, baseEnd_3643012] using wordTrace_append hprefix tailTrace_3643012
  have hstable : (prefixWord ++ tailWord_3643012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643012).length < 2 ^ (prefixWord ++ tailWord_3643012).sum := by decide
  have hdescent : baseEnd_3643012 < baseStart_3643012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643032 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 2, 2, 3]
def baseStart_3643032 : Nat := 118140960795 + 3643032 * 2 ^ 59
def prefixEnd_3643032 : Nat := 4983230072969 + 3 ^ 40 * 3643032 * 2
def baseEnd_3643032 : Nat := 1870626455710295854246007

theorem tailTrace_3643032 : CollatzResearch.WordTrace tailWord_3643032 prefixEnd_3643032 1870626455710295854246007 := by
  unfold tailWord_3643032
  simp only [CollatzResearch.WordTrace]
  refine ⟨66436146468962359588201675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88581528625283146117602233 66436146468962359588201675)
  ·
    refine ⟨99654219703443539382302513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66436146468962359588201675 99654219703443539382302513)
    ·
      refine ⟨74740664777582654536726885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99654219703443539382302513 74740664777582654536726885)
      ·
        refine ⟨14013874645796747725636291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74740664777582654536726885 14013874645796747725636291)
        ·
          refine ⟨21020811968695121588454437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14013874645796747725636291 21020811968695121588454437)
          ·
            refine ⟨3941402244130335297835207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21020811968695121588454437 3941402244130335297835207)
            ·
              refine ⟨5912103366195502946752811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3941402244130335297835207 5912103366195502946752811)
              ·
                refine ⟨8868155049293254420129217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5912103366195502946752811 8868155049293254420129217)
                ·
                  refine ⟨6651116286969940815096913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8868155049293254420129217 6651116286969940815096913)
                  ·
                    refine ⟨4988337215227455611322685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6651116286969940815096913 4988337215227455611322685)
                    ·
                      refine ⟨1870626455710295854246007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4988337215227455611322685 1870626455710295854246007)
                      ·
                        rfl

theorem cell23_3643032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_3643032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643032 prefixEnd_3643032 := by exact prefixLift 3643032
  have htrace : WordTrace (prefixWord ++ tailWord_3643032) baseStart_3643032 baseEnd_3643032 := by
    simpa [prefixWord, tailWord_3643032, baseEnd_3643032] using wordTrace_append hprefix tailTrace_3643032
  have hstable : (prefixWord ++ tailWord_3643032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643032).length < 2 ^ (prefixWord ++ tailWord_3643032).sum := by decide
  have hdescent : baseEnd_3643032 < baseStart_3643032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643055 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 4, 3, 2]
def baseStart_3643055 : Nat := 118140960795 + 3643055 * 2 ^ 59
def prefixEnd_3643055 : Nat := 4983230072969 + 3 ^ 40 * 3643055 * 2
def baseEnd_3643055 : Nat := 1870638265765349264258401

theorem tailTrace_3643055 : CollatzResearch.WordTrace tailWord_3643055 prefixEnd_3643055 1870638265765349264258401 := by
  unfold tailWord_3643055
  simp only [CollatzResearch.WordTrace]
  refine ⟨132873131816841394104490619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88582087877894262736327079 132873131816841394104490619)
  ·
    refine ⟨199309697725262091156735929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132873131816841394104490619 199309697725262091156735929)
    ·
      refine ⟨149482273293946568367551947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199309697725262091156735929 149482273293946568367551947)
      ·
        refine ⟨224223409940919852551327921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149482273293946568367551947 224223409940919852551327921)
        ·
          refine ⟨168167557455689889413495941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224223409940919852551327921 168167557455689889413495941)
          ·
            refine ⟨31531417022941854265030489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168167557455689889413495941 31531417022941854265030489)
            ·
              refine ⟨23648562767206390698772867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31531417022941854265030489 23648562767206390698772867)
              ·
                refine ⟨35472844150809586048159301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23648562767206390698772867 35472844150809586048159301)
                ·
                  refine ⟨6651158278276797384029869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35472844150809586048159301 6651158278276797384029869)
                  ·
                    refine ⟨2494184354353799019011201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6651158278276797384029869 2494184354353799019011201)
                    ·
                      refine ⟨1870638265765349264258401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494184354353799019011201 1870638265765349264258401)
                      ·
                        rfl

theorem cell23_3643055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 3, 2].length) (baseStart_3643055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643055 prefixEnd_3643055 := by exact prefixLift 3643055
  have htrace : WordTrace (prefixWord ++ tailWord_3643055) baseStart_3643055 baseEnd_3643055 := by
    simpa [prefixWord, tailWord_3643055, baseEnd_3643055] using wordTrace_append hprefix tailTrace_3643055
  have hstable : (prefixWord ++ tailWord_3643055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643055).length < 2 ^ (prefixWord ++ tailWord_3643055).sum := by decide
  have hdescent : baseEnd_3643055 < baseStart_3643055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643082 : List Nat := [3, 1, 2, 1, 5, 1, 2, 2, 1, 5]
def baseStart_3643082 : Nat := 118140960795 + 3643082 * 2 ^ 59
def prefixEnd_3643082 : Nat := 4983230072969 + 3 ^ 40 * 3643082 * 2
def baseEnd_3643082 : Nat := 623550709914340219540259

theorem tailTrace_3643082 : CollatzResearch.WordTrace tailWord_3643082 prefixEnd_3643082 623550709914340219540259 := by
  unfold tailWord_3643082
  simp only [CollatzResearch.WordTrace]
  refine ⟨33218529146935894428930875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88582744391829051810482333 33218529146935894428930875)
  ·
    refine ⟨49827793720403841643396313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33218529146935894428930875 49827793720403841643396313)
    ·
      refine ⟨37370845290302881232547235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49827793720403841643396313 37370845290302881232547235)
      ·
        refine ⟨56056267935454321848820853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37370845290302881232547235 56056267935454321848820853)
        ·
          refine ⟨5255275118948842673326955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56056267935454321848820853 5255275118948842673326955)
          ·
            refine ⟨7882912678423264009990433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5255275118948842673326955 7882912678423264009990433)
            ·
              refine ⟨5912184508817448007492825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7882912678423264009990433 5912184508817448007492825)
              ·
                refine ⟨4434138381613086005619619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5912184508817448007492825 4434138381613086005619619)
                ·
                  refine ⟨6651207572419629008429429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4434138381613086005619619 6651207572419629008429429)
                  ·
                    refine ⟨623550709914340219540259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6651207572419629008429429 623550709914340219540259)
                    ·
                      rfl

theorem cell23_3643082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_3643082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643082 prefixEnd_3643082 := by exact prefixLift 3643082
  have htrace : WordTrace (prefixWord ++ tailWord_3643082) baseStart_3643082 baseEnd_3643082 := by
    simpa [prefixWord, tailWord_3643082, baseEnd_3643082] using wordTrace_append hprefix tailTrace_3643082
  have hstable : (prefixWord ++ tailWord_3643082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643082).length < 2 ^ (prefixWord ++ tailWord_3643082).sum := by decide
  have hdescent : baseEnd_3643082 < baseStart_3643082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643148 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_3643148 : Nat := 118140960795 + 3643148 * 2 ^ 59
def prefixEnd_3643148 : Nat := 4983230072969 + 3 ^ 40 * 3643148 * 2
def baseEnd_3643148 : Nat := 1870686019466217400395473

theorem tailTrace_3643148 : CollatzResearch.WordTrace tailWord_3643148 prefixEnd_3643148 1870686019466217400395473 := by
  unfold tailWord_3643148
  simp only [CollatzResearch.WordTrace]
  refine ⟨66438261902752235493813049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88584349203669647325084065 66438261902752235493813049)
  ·
    refine ⟨49828696427064176620359787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66438261902752235493813049 49828696427064176620359787)
    ·
      refine ⟨74743044640596264930539681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49828696427064176620359787 74743044640596264930539681)
      ·
        refine ⟨56057283480447198697904761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74743044640596264930539681 56057283480447198697904761)
        ·
          refine ⟨42042962610335399023428571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56057283480447198697904761 42042962610335399023428571)
          ·
            refine ⟨63064443915503098535142857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42042962610335399023428571 63064443915503098535142857)
            ·
              refine ⟨47298332936627323901357143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63064443915503098535142857 47298332936627323901357143)
              ·
                refine ⟨70947499404940985852035715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47298332936627323901357143 70947499404940985852035715)
                ·
                  refine ⟨106421249107411478778053573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70947499404940985852035715 106421249107411478778053573)
                  ·
                    refine ⟨19953984207639652270885045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106421249107411478778053573 19953984207639652270885045)
                    ·
                      refine ⟨1870686019466217400395473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19953984207639652270885045 1870686019466217400395473)
                      ·
                        rfl

theorem cell23_3643148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_3643148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643148 prefixEnd_3643148 := by exact prefixLift 3643148
  have htrace : WordTrace (prefixWord ++ tailWord_3643148) baseStart_3643148 baseEnd_3643148 := by
    simpa [prefixWord, tailWord_3643148, baseEnd_3643148] using wordTrace_append hprefix tailTrace_3643148
  have hstable : (prefixWord ++ tailWord_3643148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643148).length < 2 ^ (prefixWord ++ tailWord_3643148).sum := by decide
  have hdescent : baseEnd_3643148 < baseStart_3643148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643169 : List Nat := [1, 2, 3, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_3643169 : Nat := 118140960795 + 3643169 * 2 ^ 59
def prefixEnd_3643169 : Nat := 4983230072969 + 3 ^ 40 * 3643169 * 2
def baseEnd_3643169 : Nat := 1870696802559961818232877

theorem tailTrace_3643169 : CollatzResearch.WordTrace tailWord_3643169 prefixEnd_3643169 1870696802559961818232877 := by
  unfold tailWord_3643169
  simp only [CollatzResearch.WordTrace]
  refine ⟨132877289738428391574140561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88584859825618927716093707 132877289738428391574140561)
  ·
    refine ⟨99657967303821293680605421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132877289738428391574140561 99657967303821293680605421)
    ·
      refine ⟨37371737738932985130227033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99657967303821293680605421 37371737738932985130227033)
      ·
        refine ⟨28028803304199738847670275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37371737738932985130227033 28028803304199738847670275)
        ·
          refine ⟨42043204956299608271505413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28028803304199738847670275 42043204956299608271505413)
          ·
            refine ⟨7883100929306176550907265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42043204956299608271505413 7883100929306176550907265)
            ·
              refine ⟨5912325696979632413180449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7883100929306176550907265 5912325696979632413180449)
              ·
                refine ⟨4434244272734724309885337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5912325696979632413180449 4434244272734724309885337)
                ·
                  refine ⟨3325683204551043232414003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4434244272734724309885337 3325683204551043232414003)
                  ·
                    refine ⟨4988524806826564848621005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3325683204551043232414003 4988524806826564848621005)
                    ·
                      refine ⟨1870696802559961818232877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4988524806826564848621005 1870696802559961818232877)
                      ·
                        rfl

theorem cell23_3643169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_3643169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643169 prefixEnd_3643169 := by exact prefixLift 3643169
  have htrace : WordTrace (prefixWord ++ tailWord_3643169) baseStart_3643169 baseEnd_3643169 := by
    simpa [prefixWord, tailWord_3643169, baseEnd_3643169] using wordTrace_append hprefix tailTrace_3643169
  have hstable : (prefixWord ++ tailWord_3643169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643169).length < 2 ^ (prefixWord ++ tailWord_3643169).sum := by decide
  have hdescent : baseEnd_3643169 < baseStart_3643169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643185 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 2, 6]
def baseStart_3643185 : Nat := 118140960795 + 3643185 * 2 ^ 59
def prefixEnd_3643185 : Nat := 4983230072969 + 3 ^ 40 * 3643185 * 2
def baseEnd_3643185 : Nat := 623568339416811251877601

theorem tailTrace_3643185 : CollatzResearch.WordTrace tailWord_3643185 prefixEnd_3643185 623568339416811251877601 := by
  unfold tailWord_3643185
  simp only [CollatzResearch.WordTrace]
  refine ⟨132877873306370426306723009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88585248870913617537815339 132877873306370426306723009)
  ·
    refine ⟨99658404979777819730042257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132877873306370426306723009 99658404979777819730042257)
    ·
      refine ⟨74743803734833364797531693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99658404979777819730042257 74743803734833364797531693)
      ·
        refine ⟨28028926400562511799074385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74743803734833364797531693 28028926400562511799074385)
        ·
          refine ⟨21021694800421883849305789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28028926400562511799074385 21021694800421883849305789)
          ·
            refine ⟨7883135550158206443489671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21021694800421883849305789 7883135550158206443489671)
            ·
              refine ⟨11824703325237309665234507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7883135550158206443489671 11824703325237309665234507)
              ·
                refine ⟨17737054987855964497851761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11824703325237309665234507 17737054987855964497851761)
                ·
                  refine ⟨13302791240891973373388821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17737054987855964497851761 13302791240891973373388821)
                  ·
                    refine ⟨623568339416811251877601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13302791240891973373388821 623568339416811251877601)
                    ·
                      rfl

theorem cell23_3643185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_3643185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643185 prefixEnd_3643185 := by exact prefixLift 3643185
  have htrace : WordTrace (prefixWord ++ tailWord_3643185) baseStart_3643185 baseEnd_3643185 := by
    simpa [prefixWord, tailWord_3643185, baseEnd_3643185] using wordTrace_append hprefix tailTrace_3643185
  have hstable : (prefixWord ++ tailWord_3643185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643185).length < 2 ^ (prefixWord ++ tailWord_3643185).sum := by decide
  have hdescent : baseEnd_3643185 < baseStart_3643185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643192 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 1, 4, 2]
def baseStart_3643192 : Nat := 118140960795 + 3643192 * 2 ^ 59
def prefixEnd_3643192 : Nat := 4983230072969 + 3 ^ 40 * 3643192 * 2
def baseEnd_3643192 : Nat := 1870708612615015228245271

theorem tailTrace_3643192 : CollatzResearch.WordTrace tailWord_3643192 prefixEnd_3643192 1870708612615015228245271 := by
  unfold tailWord_3643192
  simp only [CollatzResearch.WordTrace]
  refine ⟨66439064308672533251113915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88585419078230044334818553 66439064308672533251113915)
  ·
    refine ⟨99658596463008799876670873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66439064308672533251113915 99658596463008799876670873)
    ·
      refine ⟨74743947347256599907503155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99658596463008799876670873 74743947347256599907503155)
      ·
        refine ⟨112115921020884899861254733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74743947347256599907503155 112115921020884899861254733)
        ·
          refine ⟨42043470382831837447970525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112115921020884899861254733 42043470382831837447970525)
          ·
            refine ⟨15766301393561939042988947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42043470382831837447970525 15766301393561939042988947)
            ·
              refine ⟨23649452090342908564483421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15766301393561939042988947 23649452090342908564483421)
              ·
                refine ⟨8868544533878590711681283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23649452090342908564483421 8868544533878590711681283)
                ·
                  refine ⟨13302816800817886067521925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8868544533878590711681283 13302816800817886067521925)
                  ·
                    refine ⟨2494278150153353637660361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13302816800817886067521925 2494278150153353637660361)
                    ·
                      refine ⟨1870708612615015228245271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494278150153353637660361 1870708612615015228245271)
                      ·
                        rfl

theorem cell23_3643192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 1, 4, 2].length) (baseStart_3643192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643192 prefixEnd_3643192 := by exact prefixLift 3643192
  have htrace : WordTrace (prefixWord ++ tailWord_3643192) baseStart_3643192 baseEnd_3643192 := by
    simpa [prefixWord, tailWord_3643192, baseEnd_3643192] using wordTrace_append hprefix tailTrace_3643192
  have hstable : (prefixWord ++ tailWord_3643192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643192).length < 2 ^ (prefixWord ++ tailWord_3643192).sum := by decide
  have hdescent : baseEnd_3643192 < baseStart_3643192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643213 : List Nat := [1, 6, 1, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_3643213 : Nat := 118140960795 + 3643213 * 2 ^ 59
def prefixEnd_3643213 : Nat := 4983230072969 + 3 ^ 40 * 3643213 * 2
def baseEnd_3643213 : Nat := 1870719395708759646082675

theorem tailTrace_3643213 : CollatzResearch.WordTrace tailWord_3643213 prefixEnd_3643213 1870719395708759646082675 := by
  unfold tailWord_3643213
  simp only [CollatzResearch.WordTrace]
  refine ⟨132878894550268987088742293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88585929700179324725828195 132878894550268987088742293)
  ·
    refine ⟨6228698182043858769784795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132878894550268987088742293 6228698182043858769784795)
    ·
      refine ⟨9343047273065788154677193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6228698182043858769784795 9343047273065788154677193)
      ·
        refine ⟨7007285454799341116007895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9343047273065788154677193 7007285454799341116007895)
        ·
          refine ⟨10510928182199011674011843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7007285454799341116007895 10510928182199011674011843)
          ·
            refine ⟨15766392273298517511017765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10510928182199011674011843 15766392273298517511017765)
            ·
              refine ⟨2956198551243472033315831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15766392273298517511017765 2956198551243472033315831)
              ·
                refine ⟨4434297826865208049973747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956198551243472033315831 4434297826865208049973747)
                ·
                  refine ⟨6651446740297812074960621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4434297826865208049973747 6651446740297812074960621)
                  ·
                    refine ⟨2494292527611679528110233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6651446740297812074960621 2494292527611679528110233)
                    ·
                      refine ⟨1870719395708759646082675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494292527611679528110233 1870719395708759646082675)
                      ·
                        rfl

theorem cell23_3643213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_3643213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643213 prefixEnd_3643213 := by exact prefixLift 3643213
  have htrace : WordTrace (prefixWord ++ tailWord_3643213) baseStart_3643213 baseEnd_3643213 := by
    simpa [prefixWord, tailWord_3643213, baseEnd_3643213] using wordTrace_append hprefix tailTrace_3643213
  have hstable : (prefixWord ++ tailWord_3643213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643213).length < 2 ^ (prefixWord ++ tailWord_3643213).sum := by decide
  have hdescent : baseEnd_3643213 < baseStart_3643213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643225 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 4, 3, 3]
def baseStart_3643225 : Nat := 118140960795 + 3643225 * 2 ^ 59
def prefixEnd_3643225 : Nat := 4983230072969 + 3 ^ 40 * 3643225 * 2
def baseEnd_3643225 : Nat := 1870725557476613599132619

theorem tailTrace_3643225 : CollatzResearch.WordTrace tailWord_3643225 prefixEnd_3643225 1870725557476613599132619 := by
  unfold tailWord_3643225
  simp only [CollatzResearch.WordTrace]
  refine ⟨132879332226225513138179129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88586221484150342092119419 132879332226225513138179129)
  ·
    refine ⟨99659499169669134853634347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132879332226225513138179129 99659499169669134853634347)
    ·
      refine ⟨149489248754503702280451521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99659499169669134853634347 149489248754503702280451521)
      ·
        refine ⟨112116936565877776710338641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149489248754503702280451521 112116936565877776710338641)
        ·
          refine ⟨84087702424408332532753981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112116936565877776710338641 84087702424408332532753981)
          ·
            refine ⟨31532888409153124699782743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84087702424408332532753981 31532888409153124699782743)
            ·
              refine ⟨47299332613729687049674115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31532888409153124699782743 47299332613729687049674115)
              ·
                refine ⟨70948998920594530574511173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47299332613729687049674115 70948998920594530574511173)
                ·
                  refine ⟨13302937297611474482720845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70948998920594530574511173 13302937297611474482720845)
                  ·
                    refine ⟨4988601486604302931020317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13302937297611474482720845 4988601486604302931020317)
                    ·
                      refine ⟨1870725557476613599132619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4988601486604302931020317 1870725557476613599132619)
                      ·
                        rfl

theorem cell23_3643225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_3643225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643225 prefixEnd_3643225 := by exact prefixLift 3643225
  have htrace : WordTrace (prefixWord ++ tailWord_3643225) baseStart_3643225 baseEnd_3643225 := by
    simpa [prefixWord, tailWord_3643225, baseEnd_3643225] using wordTrace_append hprefix tailTrace_3643225
  have hstable : (prefixWord ++ tailWord_3643225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643225).length < 2 ^ (prefixWord ++ tailWord_3643225).sum := by decide
  have hdescent : baseEnd_3643225 < baseStart_3643225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643232 : List Nat := [2, 1, 1, 3, 3, 2, 2, 4, 5]
def baseStart_3643232 : Nat := 118140960795 + 3643232 * 2 ^ 59
def prefixEnd_3643232 : Nat := 4983230072969 + 3 ^ 40 * 3643232 * 2
def baseEnd_3643232 : Nat := 207858794649021674638343

theorem tailTrace_3643232 : CollatzResearch.WordTrace tailWord_3643232 prefixEnd_3643232 207858794649021674638343 := by
  unfold tailWord_3643232
  simp only [CollatzResearch.WordTrace]
  refine ⟨66439793768600076666841975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88586391691466768889122633 66439793768600076666841975)
  ·
    refine ⟨99659690652900115000262963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66439793768600076666841975 99659690652900115000262963)
    ·
      refine ⟨149489535979350172500394445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99659690652900115000262963 149489535979350172500394445)
      ·
        refine ⟨56058575992256314687647917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149489535979350172500394445 56058575992256314687647917)
        ·
          refine ⟨21021965997096118007867969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56058575992256314687647917 21021965997096118007867969)
          ·
            refine ⟨15766474497822088505900977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21021965997096118007867969 15766474497822088505900977)
            ·
              refine ⟨11824855873366566379425733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15766474497822088505900977 11824855873366566379425733)
              ·
                refine ⟨2217160476256231196142325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11824855873366566379425733 2217160476256231196142325)
                ·
                  refine ⟨207858794649021674638343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2217160476256231196142325 207858794649021674638343)
                  ·
                    rfl

theorem cell23_3643232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 5].length) (baseStart_3643232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643232 prefixEnd_3643232 := by exact prefixLift 3643232
  have htrace : WordTrace (prefixWord ++ tailWord_3643232) baseStart_3643232 baseEnd_3643232 := by
    simpa [prefixWord, tailWord_3643232, baseEnd_3643232] using wordTrace_append hprefix tailTrace_3643232
  have hstable : (prefixWord ++ tailWord_3643232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643232).length < 2 ^ (prefixWord ++ tailWord_3643232).sum := by decide
  have hdescent : baseEnd_3643232 < baseStart_3643232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643245 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_3643245 : Nat := 118140960795 + 3643245 * 2 ^ 59
def prefixEnd_3643245 : Nat := 4983230072969 + 3 ^ 40 * 3643245 * 2
def baseEnd_3643245 : Nat := 623578609029901173627509

theorem tailTrace_3643245 : CollatzResearch.WordTrace tailWord_3643245 prefixEnd_3643245 623578609029901173627509 := by
  unfold tailWord_3643245
  simp only [CollatzResearch.WordTrace]
  refine ⟨132880061686153056553907189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88586707790768704369271459 132880061686153056553907189)
  ·
    refine ⟨12457505783076849051928799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132880061686153056553907189 12457505783076849051928799)
    ·
      refine ⟨18686258674615273577893199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12457505783076849051928799 18686258674615273577893199)
      ·
        refine ⟨28029388011922910366839799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18686258674615273577893199 28029388011922910366839799)
        ·
          refine ⟨42044082017884365550259699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28029388011922910366839799 42044082017884365550259699)
          ·
            refine ⟨63066123026826548325389549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42044082017884365550259699 63066123026826548325389549)
            ·
              refine ⟨23649796135059955622021081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63066123026826548325389549 23649796135059955622021081)
              ·
                refine ⟨17737347101294966716515811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23649796135059955622021081 17737347101294966716515811)
                ·
                  refine ⟨26606020651942450074773717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17737347101294966716515811 26606020651942450074773717)
                  ·
                    refine ⟨623578609029901173627509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26606020651942450074773717 623578609029901173627509)
                    ·
                      rfl

theorem cell23_3643245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_3643245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643245 prefixEnd_3643245 := by exact prefixLift 3643245
  have htrace : WordTrace (prefixWord ++ tailWord_3643245) baseStart_3643245 baseEnd_3643245 := by
    simpa [prefixWord, tailWord_3643245, baseEnd_3643245] using wordTrace_append hprefix tailTrace_3643245
  have hstable : (prefixWord ++ tailWord_3643245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643245).length < 2 ^ (prefixWord ++ tailWord_3643245).sum := by decide
  have hdescent : baseEnd_3643245 < baseStart_3643245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643294 : List Nat := [4, 3, 1, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3643294 : Nat := 118140960795 + 3643294 * 2 ^ 59
def prefixEnd_3643294 : Nat := 4983230072969 + 3 ^ 40 * 3643294 * 2
def baseEnd_3643294 : Nat := 1870760987641773829169803

theorem tailTrace_3643294 : CollatzResearch.WordTrace tailWord_3643294 prefixEnd_3643294 1870760987641773829169803 := by
  unfold tailWord_3643294
  simp only [CollatzResearch.WordTrace]
  refine ⟨16610231107871942240305117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88587899241983691948293957 16610231107871942240305117)
  ·
    refine ⟨6228836665451978340114419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16610231107871942240305117 6228836665451978340114419)
    ·
      refine ⟨9343254998177967510171629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6228836665451978340114419 9343254998177967510171629)
      ·
        refine ⟨3503720624316737816314361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9343254998177967510171629 3503720624316737816314361)
        ·
          refine ⟨2627790468237553362235771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3503720624316737816314361 2627790468237553362235771)
          ·
            refine ⟨3941685702356330043353657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2627790468237553362235771 3941685702356330043353657)
            ·
              refine ⟨2956264276767247532515243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3941685702356330043353657 2956264276767247532515243)
              ·
                refine ⟨4434396415150871298772865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956264276767247532515243 4434396415150871298772865)
                ·
                  refine ⟨3325797311363153474079649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4434396415150871298772865 3325797311363153474079649)
                  ·
                    refine ⟨2494347983522365105559737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3325797311363153474079649 2494347983522365105559737)
                    ·
                      refine ⟨1870760987641773829169803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494347983522365105559737 1870760987641773829169803)
                      ·
                        rfl

theorem cell23_3643294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3643294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643294 prefixEnd_3643294 := by exact prefixLift 3643294
  have htrace : WordTrace (prefixWord ++ tailWord_3643294) baseStart_3643294 baseEnd_3643294 := by
    simpa [prefixWord, tailWord_3643294, baseEnd_3643294] using wordTrace_append hprefix tailTrace_3643294
  have hstable : (prefixWord ++ tailWord_3643294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643294).length < 2 ^ (prefixWord ++ tailWord_3643294).sum := by decide
  have hdescent : baseEnd_3643294 < baseStart_3643294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643392 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 3]
def baseStart_3643392 : Nat := 118140960795 + 3643392 * 2 ^ 59
def prefixEnd_3643392 : Nat := 4983230072969 + 3 ^ 40 * 3643392 * 2
def baseEnd_3643392 : Nat := 1870811308745914445744351

theorem tailTrace_3643392 : CollatzResearch.WordTrace tailWord_3643392 prefixEnd_3643392 1870811308745914445744351 := by
  unfold tailWord_3643392
  simp only [CollatzResearch.WordTrace]
  refine ⟨66442711608310250329754215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88590282144413667106338953 66442711608310250329754215)
  ·
    refine ⟨99664067412465375494631323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66442711608310250329754215 99664067412465375494631323)
    ·
      refine ⟨149496101118698063241946985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99664067412465375494631323 149496101118698063241946985)
      ·
        refine ⟨112122075839023547431460239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149496101118698063241946985 112122075839023547431460239)
        ·
          refine ⟨168183113758535321147190359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112122075839023547431460239 168183113758535321147190359)
          ·
            refine ⟨252274670637802981720785539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168183113758535321147190359 252274670637802981720785539)
            ·
              refine ⟨378412005956704472581178309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252274670637802981720785539 378412005956704472581178309)
              ·
                refine ⟨70952251116882088608970933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378412005956704472581178309 70952251116882088608970933)
                ·
                  refine ⟨6651773542207695807091025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70952251116882088608970933 6651773542207695807091025)
                  ·
                    refine ⟨4988830156655771855318269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6651773542207695807091025 4988830156655771855318269)
                    ·
                      refine ⟨1870811308745914445744351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4988830156655771855318269 1870811308745914445744351)
                      ·
                        rfl

theorem cell23_3643392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_3643392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643392 prefixEnd_3643392 := by exact prefixLift 3643392
  have htrace : WordTrace (prefixWord ++ tailWord_3643392) baseStart_3643392 baseEnd_3643392 := by
    simpa [prefixWord, tailWord_3643392, baseEnd_3643392] using wordTrace_append hprefix tailTrace_3643392
  have hstable : (prefixWord ++ tailWord_3643392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643392).length < 2 ^ (prefixWord ++ tailWord_3643392).sum := by decide
  have hdescent : baseEnd_3643392 < baseStart_3643392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643399 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 4, 4]
def baseStart_3643399 : Nat := 118140960795 + 3643399 * 2 ^ 59
def prefixEnd_3643399 : Nat := 4983230072969 + 3 ^ 40 * 3643399 * 2
def baseEnd_3643399 : Nat := 623604967703498639452273

theorem tailTrace_3643399 : CollatzResearch.WordTrace tailWord_3643399 prefixEnd_3643399 623604967703498639452273 := by
  unfold tailWord_3643399
  simp only [CollatzResearch.WordTrace]
  refine ⟨132885678527595140855013251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88590452351730093903342167 132885678527595140855013251)
  ·
    refine ⟨199328517791392711282519877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132885678527595140855013251 199328517791392711282519877)
    ·
      refine ⟨37374097085886133365472477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199328517791392711282519877 37374097085886133365472477)
      ·
        refine ⟨14015286407207300012052179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37374097085886133365472477 14015286407207300012052179)
        ·
          refine ⟨21022929610810950018078269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14015286407207300012052179 21022929610810950018078269)
          ·
            refine ⟨7883598604054106256779351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21022929610810950018078269 7883598604054106256779351)
            ·
              refine ⟨11825397906081159385169027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7883598604054106256779351 11825397906081159385169027)
              ·
                refine ⟨17738096859121739077753541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11825397906081159385169027 17738096859121739077753541)
                ·
                  refine ⟨3325893161085326077078789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17738096859121739077753541 3325893161085326077078789)
                  ·
                    refine ⟨623604967703498639452273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3325893161085326077078789 623604967703498639452273)
                    ·
                      rfl

theorem cell23_3643399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_3643399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643399 prefixEnd_3643399 := by exact prefixLift 3643399
  have htrace : WordTrace (prefixWord ++ tailWord_3643399) baseStart_3643399 baseEnd_3643399 := by
    simpa [prefixWord, tailWord_3643399, baseEnd_3643399] using wordTrace_append hprefix tailTrace_3643399
  have hstable : (prefixWord ++ tailWord_3643399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643399).length < 2 ^ (prefixWord ++ tailWord_3643399).sum := by decide
  have hdescent : baseEnd_3643399 < baseStart_3643399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643416 : List Nat := [2, 1, 2, 3, 2, 1, 5, 1, 2, 4]
def baseStart_3643416 : Nat := 118140960795 + 3643416 * 2 ^ 59
def prefixEnd_3643416 : Nat := 4983230072969 + 3 ^ 40 * 3643416 * 2
def baseEnd_3643416 : Nat := 623607877427207450614747

theorem tailTrace_3643416 : CollatzResearch.WordTrace tailWord_3643416 prefixEnd_3643416 623607877427207450614747 := by
  unfold tailWord_3643416
  simp only [CollatzResearch.WordTrace]
  refine ⟨66443149284266776379191051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88590865712355701838921401 66443149284266776379191051)
  ·
    refine ⟨99664723926400164568786577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66443149284266776379191051 99664723926400164568786577)
    ·
      refine ⟨74748542944800123426589933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99664723926400164568786577 74748542944800123426589933)
      ·
        refine ⟨28030703604300046284971225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74748542944800123426589933 28030703604300046284971225)
        ·
          refine ⟨21023027703225034713728419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28030703604300046284971225 21023027703225034713728419)
          ·
            refine ⟨31534541554837552070592629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21023027703225034713728419 31534541554837552070592629)
            ·
              refine ⟨2956363270766020506618059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31534541554837552070592629 2956363270766020506618059)
              ·
                refine ⟨4434544906149030759927089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956363270766020506618059 4434544906149030759927089)
                ·
                  refine ⟨3325908679611773069945317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4434544906149030759927089 3325908679611773069945317)
                  ·
                    refine ⟨623607877427207450614747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3325908679611773069945317 623607877427207450614747)
                    ·
                      rfl

theorem cell23_3643416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 2, 4].length) (baseStart_3643416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643416 prefixEnd_3643416 := by exact prefixLift 3643416
  have htrace : WordTrace (prefixWord ++ tailWord_3643416) baseStart_3643416 baseEnd_3643416 := by
    simpa [prefixWord, tailWord_3643416, baseEnd_3643416] using wordTrace_append hprefix tailTrace_3643416
  have hstable : (prefixWord ++ tailWord_3643416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643416).length < 2 ^ (prefixWord ++ tailWord_3643416).sum := by decide
  have hdescent : baseEnd_3643416 < baseStart_3643416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643426 : List Nat := [3, 3, 1, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_3643426 : Nat := 118140960795 + 3643426 * 2 ^ 59
def prefixEnd_3643426 : Nat := 4983230072969 + 3 ^ 40 * 3643426 * 2
def baseEnd_3643426 : Nat := 1870828767088167312719195

theorem tailTrace_3643426 : CollatzResearch.WordTrace tailWord_3643426 prefixEnd_3643426 1870828767088167312719195 := by
  unfold tailWord_3643426
  simp only [CollatzResearch.WordTrace]
  refine ⟨33221665824624331116561533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88591108865664882977497421 33221665824624331116561533)
  ·
    refine ⟨12458124684234124168710575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33221665824624331116561533 12458124684234124168710575)
    ·
      refine ⟨18687187026351186253065863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12458124684234124168710575 18687187026351186253065863)
      ·
        refine ⟨28030780539526779379598795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18687187026351186253065863 28030780539526779379598795)
        ·
          refine ⟨42046170809290169069398193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28030780539526779379598795 42046170809290169069398193)
          ·
            refine ⟨31534628106967626802048645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42046170809290169069398193 31534628106967626802048645)
            ·
              refine ⟨5912742770056430025384121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31534628106967626802048645 5912742770056430025384121)
              ·
                refine ⟨4434557077542322519038091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5912742770056430025384121 4434557077542322519038091)
                ·
                  refine ⟨6651835616313483778557137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4434557077542322519038091 6651835616313483778557137)
                  ·
                    refine ⟨4988876712235112833917853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6651835616313483778557137 4988876712235112833917853)
                    ·
                      refine ⟨1870828767088167312719195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4988876712235112833917853 1870828767088167312719195)
                      ·
                        rfl

theorem cell23_3643426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_3643426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643426 prefixEnd_3643426 := by exact prefixLift 3643426
  have htrace : WordTrace (prefixWord ++ tailWord_3643426) baseStart_3643426 baseEnd_3643426 := by
    simpa [prefixWord, tailWord_3643426, baseEnd_3643426] using wordTrace_append hprefix tailTrace_3643426
  have hstable : (prefixWord ++ tailWord_3643426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643426).length < 2 ^ (prefixWord ++ tailWord_3643426).sum := by decide
  have hdescent : baseEnd_3643426 < baseStart_3643426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643429 : List Nat := [1, 3, 1, 2, 2, 5, 2, 7]
def baseStart_3643429 : Nat := 118140960795 + 3643429 * 2 ^ 59
def prefixEnd_3643429 : Nat := 4983230072969 + 3 ^ 40 * 3643429 * 2
def baseEnd_3643429 : Nat := 69290011390004844480803

theorem tailTrace_3643429 : CollatzResearch.WordTrace tailWord_3643429 prefixEnd_3643429 69290011390004844480803 := by
  unfold tailWord_3643429
  simp only [CollatzResearch.WordTrace]
  refine ⟨132886772717486455978605341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88591181811657637319070227 132886772717486455978605341)
  ·
    refine ⟨49832539769057420991977003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132886772717486455978605341 49832539769057420991977003)
    ·
      refine ⟨74748809653586131487965505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49832539769057420991977003 74748809653586131487965505)
      ·
        refine ⟨56061607240189598615974129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74748809653586131487965505 56061607240189598615974129)
        ·
          refine ⟨42046205430142198961980597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56061607240189598615974129 42046205430142198961980597)
          ·
            refine ⟨3941831759075831152685681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42046205430142198961980597 3941831759075831152685681)
            ·
              refine ⟨2956373819306873364514261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3941831759075831152685681 2956373819306873364514261)
              ·
                refine ⟨69290011390004844480803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2956373819306873364514261 69290011390004844480803)
                ·
                  rfl

theorem cell23_3643429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 7].length) (baseStart_3643429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643429 prefixEnd_3643429 := by exact prefixLift 3643429
  have htrace : WordTrace (prefixWord ++ tailWord_3643429) baseStart_3643429 baseEnd_3643429 := by
    simpa [prefixWord, tailWord_3643429, baseEnd_3643429] using wordTrace_append hprefix tailTrace_3643429
  have hstable : (prefixWord ++ tailWord_3643429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643429).length < 2 ^ (prefixWord ++ tailWord_3643429).sum := by decide
  have hdescent : baseEnd_3643429 < baseStart_3643429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643440 : List Nat := [2, 1, 1, 1, 2, 7, 1, 3, 1, 2, 2]
def baseStart_3643440 : Nat := 118140960795 + 3643440 * 2 ^ 59
def prefixEnd_3643440 : Nat := 4983230072969 + 3 ^ 40 * 3643440 * 2
def baseEnd_3643440 : Nat := 1870835955817330257944131

theorem tailTrace_3643440 : CollatzResearch.WordTrace tailWord_3643440 prefixEnd_3643440 1870835955817330257944131 := by
  unfold tailWord_3643440
  simp only [CollatzResearch.WordTrace]
  refine ⟨66443586960223302428627887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88591449280297736571503849 66443586960223302428627887)
  ·
    refine ⟨99665380440334953642941831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66443586960223302428627887 99665380440334953642941831)
    ·
      refine ⟨149498070660502430464412747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99665380440334953642941831 149498070660502430464412747)
      ·
        refine ⟨224247105990753645696619121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149498070660502430464412747 224247105990753645696619121)
        ·
          refine ⟨168185329493065234272464341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224247105990753645696619121 168185329493065234272464341)
          ·
            refine ⟨3941843659993716428260883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 168185329493065234272464341 3941843659993716428260883)
            ·
              refine ⟨5912765489990574642391325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3941843659993716428260883 5912765489990574642391325)
              ·
                refine ⟨2217287058746465490896747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5912765489990574642391325 2217287058746465490896747)
                ·
                  refine ⟨3325930588119698236345121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217287058746465490896747 3325930588119698236345121)
                  ·
                    refine ⟨2494447941089773677258841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3325930588119698236345121 2494447941089773677258841)
                    ·
                      refine ⟨1870835955817330257944131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494447941089773677258841 1870835955817330257944131)
                      ·
                        rfl

theorem cell23_3643440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 3, 1, 2, 2].length) (baseStart_3643440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643440 prefixEnd_3643440 := by exact prefixLift 3643440
  have htrace : WordTrace (prefixWord ++ tailWord_3643440) baseStart_3643440 baseEnd_3643440 := by
    simpa [prefixWord, tailWord_3643440, baseEnd_3643440] using wordTrace_append hprefix tailTrace_3643440
  have hstable : (prefixWord ++ tailWord_3643440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643440).length < 2 ^ (prefixWord ++ tailWord_3643440).sum := by decide
  have hdescent : baseEnd_3643440 < baseStart_3643440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643452 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_3643452 : Nat := 118140960795 + 3643452 * 2 ^ 59
def prefixEnd_3643452 : Nat := 4983230072969 + 3 ^ 40 * 3643452 * 2
def baseEnd_3643452 : Nat := 1870842117585184210994075

theorem tailTrace_3643452 : CollatzResearch.WordTrace tailWord_3643452 prefixEnd_3643452 1870842117585184210994075 := by
  unfold tailWord_3643452
  simp only [CollatzResearch.WordTrace]
  refine ⟨66443805798201565453346305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88591741064268753937795073 66443805798201565453346305)
  ·
    refine ⟨49832854348651174090009729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66443805798201565453346305 49832854348651174090009729)
    ·
      refine ⟨37374640761488380567507297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49832854348651174090009729 37374640761488380567507297)
      ·
        refine ⟨28030980571116285425630473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37374640761488380567507297 28030980571116285425630473)
        ·
          refine ⟨21023235428337214069222855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28030980571116285425630473 21023235428337214069222855)
          ·
            refine ⟨31534853142505821103834283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21023235428337214069222855 31534853142505821103834283)
            ·
              refine ⟨47302279713758731655751425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31534853142505821103834283 47302279713758731655751425)
              ·
                refine ⟨35476709785319048741813569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47302279713758731655751425 35476709785319048741813569)
                ·
                  refine ⟨26607532338989286556360177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35476709785319048741813569 26607532338989286556360177)
                  ·
                    refine ⟨19955649254241964917270133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26607532338989286556360177 19955649254241964917270133)
                    ·
                      refine ⟨1870842117585184210994075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19955649254241964917270133 1870842117585184210994075)
                      ·
                        rfl

theorem cell23_3643452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_3643452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643452 prefixEnd_3643452 := by exact prefixLift 3643452
  have htrace : WordTrace (prefixWord ++ tailWord_3643452) baseStart_3643452 baseEnd_3643452 := by
    simpa [prefixWord, tailWord_3643452, baseEnd_3643452] using wordTrace_append hprefix tailTrace_3643452
  have hstable : (prefixWord ++ tailWord_3643452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643452).length < 2 ^ (prefixWord ++ tailWord_3643452).sum := by decide
  have hdescent : baseEnd_3643452 < baseStart_3643452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643457 : List Nat := [1, 2, 5, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_3643457 : Nat := 118140960795 + 3643457 * 2 ^ 59
def prefixEnd_3643457 : Nat := 4983230072969 + 3 ^ 40 * 3643457 * 2
def baseEnd_3643457 : Nat := 1870844684988456691431553

theorem tailTrace_3643457 : CollatzResearch.WordTrace tailWord_3643457 prefixEnd_3643457 1870844684988456691431553 := by
  unfold tailWord_3643457
  simp only [CollatzResearch.WordTrace]
  refine ⟨132887793961385016760624625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88591862640923344507083083 132887793961385016760624625)
  ·
    refine ⟨99665845471038762570468469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132887793961385016760624625 99665845471038762570468469)
    ·
      refine ⟨9343673012909883990981419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99665845471038762570468469 9343673012909883990981419)
      ·
        refine ⟨14015509519364825986472129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9343673012909883990981419 14015509519364825986472129)
        ·
          refine ⟨10511632139523619489854097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14015509519364825986472129 10511632139523619489854097)
          ·
            refine ⟨7883724104642714617390573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10511632139523619489854097 7883724104642714617390573)
            ·
              refine ⟨2956396539241017981521465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7883724104642714617390573 2956396539241017981521465)
              ·
                refine ⟨2217297404430763486141099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2956396539241017981521465 2217297404430763486141099)
                ·
                  refine ⟨3325946106646145229211649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217297404430763486141099 3325946106646145229211649)
                  ·
                    refine ⟨2494459579984608921908737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3325946106646145229211649 2494459579984608921908737)
                    ·
                      refine ⟨1870844684988456691431553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494459579984608921908737 1870844684988456691431553)
                      ·
                        rfl

theorem cell23_3643457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_3643457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643457 prefixEnd_3643457 := by exact prefixLift 3643457
  have htrace : WordTrace (prefixWord ++ tailWord_3643457) baseStart_3643457 baseEnd_3643457 := by
    simpa [prefixWord, tailWord_3643457, baseEnd_3643457] using wordTrace_append hprefix tailTrace_3643457
  have hstable : (prefixWord ++ tailWord_3643457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643457).length < 2 ^ (prefixWord ++ tailWord_3643457).sum := by decide
  have hdescent : baseEnd_3643457 < baseStart_3643457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643482 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_3643482 : Nat := 118140960795 + 3643482 * 2 ^ 59
def prefixEnd_3643482 : Nat := 4983230072969 + 3 ^ 40 * 3643482 * 2
def baseEnd_3643482 : Nat := 1870857522004819093618937

theorem tailTrace_3643482 : CollatzResearch.WordTrace tailWord_3643482 prefixEnd_3643482 1870857522004819093618937 := by
  unfold tailWord_3643482
  simp only [CollatzResearch.WordTrace]
  refine ⟨33222176446573611507571175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88592470524196297353523133 33222176446573611507571175)
  ·
    refine ⟨49833264669860417261356763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33222176446573611507571175 49833264669860417261356763)
    ·
      refine ⟨74749897004790625892035145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49833264669860417261356763 74749897004790625892035145)
      ·
        refine ⟨56062422753592969419026359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74749897004790625892035145 56062422753592969419026359)
        ·
          refine ⟨84093634130389454128539539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56062422753592969419026359 84093634130389454128539539)
          ·
            refine ⟨126140451195584181192809309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84093634130389454128539539 126140451195584181192809309)
            ·
              refine ⟨47302669198344067947303491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126140451195584181192809309 47302669198344067947303491)
              ·
                refine ⟨70954003797516101920955237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47302669198344067947303491 70954003797516101920955237)
                ·
                  refine ⟨13303875712034269110179107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70954003797516101920955237 13303875712034269110179107)
                  ·
                    refine ⟨19955813568051403665268661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13303875712034269110179107 19955813568051403665268661)
                    ·
                      refine ⟨1870857522004819093618937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19955813568051403665268661 1870857522004819093618937)
                      ·
                        rfl

theorem cell23_3643482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_3643482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643482 prefixEnd_3643482 := by exact prefixLift 3643482
  have htrace : WordTrace (prefixWord ++ tailWord_3643482) baseStart_3643482 baseEnd_3643482 := by
    simpa [prefixWord, tailWord_3643482, baseEnd_3643482] using wordTrace_append hprefix tailTrace_3643482
  have hstable : (prefixWord ++ tailWord_3643482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643482).length < 2 ^ (prefixWord ++ tailWord_3643482).sum := by decide
  have hdescent : baseEnd_3643482 < baseStart_3643482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643513 : List Nat := [1, 2, 1, 3, 4, 1, 1, 4, 2, 2, 2]
def baseStart_3643513 : Nat := 118140960795 + 3643513 * 2 ^ 59
def prefixEnd_3643513 : Nat := 4983230072969 + 3 ^ 40 * 3643513 * 2
def baseEnd_3643513 : Nat := 1870873439905108472331295

theorem tailTrace_3643513 : CollatzResearch.WordTrace tailWord_3643513 prefixEnd_3643513 1870873439905108472331295 := by
  unfold tailWord_3643513
  simp only [CollatzResearch.WordTrace]
  refine ⟨132889836449182138324663193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88593224299454758883108795 132889836449182138324663193)
  ·
    refine ⟨99667377336886603743497395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132889836449182138324663193 99667377336886603743497395)
    ·
      refine ⟨149501066005329905615246093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99667377336886603743497395 149501066005329905615246093)
      ·
        refine ⟨56062899751998714605717285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149501066005329905615246093 56062899751998714605717285)
        ·
          refine ⟨10511793703499758988571991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56062899751998714605717285 10511793703499758988571991)
          ·
            refine ⟨15767690555249638482857987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10511793703499758988571991 15767690555249638482857987)
            ·
              refine ⟨23651535832874457724286981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15767690555249638482857987 23651535832874457724286981)
              ·
                refine ⟨4434662968663960823303809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23651535832874457724286981 4434662968663960823303809)
                ·
                  refine ⟨3325997226497970617477857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4434662968663960823303809 3325997226497970617477857)
                  ·
                    refine ⟨2494497919873477963108393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3325997226497970617477857 2494497919873477963108393)
                    ·
                      refine ⟨1870873439905108472331295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494497919873477963108393 1870873439905108472331295)
                      ·
                        rfl

theorem cell23_3643513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_3643513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643513 prefixEnd_3643513 := by exact prefixLift 3643513
  have htrace : WordTrace (prefixWord ++ tailWord_3643513) baseStart_3643513 baseEnd_3643513 := by
    simpa [prefixWord, tailWord_3643513, baseEnd_3643513] using wordTrace_append hprefix tailTrace_3643513
  have hstable : (prefixWord ++ tailWord_3643513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643513).length < 2 ^ (prefixWord ++ tailWord_3643513).sum := by decide
  have hdescent : baseEnd_3643513 < baseStart_3643513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643529 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 2, 3, 3]
def baseStart_3643529 : Nat := 118140960795 + 3643529 * 2 ^ 59
def prefixEnd_3643529 : Nat := 4983230072969 + 3 ^ 40 * 3643529 * 2
def baseEnd_3643529 : Nat := 1870881655595580409731221

theorem tailTrace_3643529 : CollatzResearch.WordTrace tailWord_3643529 prefixEnd_3643529 1870881655595580409731221 := by
  unfold tailWord_3643529
  simp only [CollatzResearch.WordTrace]
  refine ⟨132890420017124173057245641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88593613344749448704830427 132890420017124173057245641)
  ·
    refine ⟨99667815012843129792934231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132890420017124173057245641 99667815012843129792934231)
    ·
      refine ⟨149501722519264694689401347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99667815012843129792934231 149501722519264694689401347)
      ·
        refine ⟨224252583778897042034102021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149501722519264694689401347 224252583778897042034102021)
        ·
          refine ⟨42047359458543195381394129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224252583778897042034102021 42047359458543195381394129)
          ·
            refine ⟨31535519593907396536045597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42047359458543195381394129 31535519593907396536045597)
            ·
              refine ⟨11825819847715273701017099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31535519593907396536045597 11825819847715273701017099)
              ·
                refine ⟨17738729771572910551525649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11825819847715273701017099 17738729771572910551525649)
                ·
                  refine ⟨13304047328679682913644237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17738729771572910551525649 13304047328679682913644237)
                  ·
                    refine ⟨4989017748254881092616589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13304047328679682913644237 4989017748254881092616589)
                    ·
                      refine ⟨1870881655595580409731221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4989017748254881092616589 1870881655595580409731221)
                      ·
                        rfl

theorem cell23_3643529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 3, 3].length) (baseStart_3643529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643529 prefixEnd_3643529 := by exact prefixLift 3643529
  have htrace : WordTrace (prefixWord ++ tailWord_3643529) baseStart_3643529 baseEnd_3643529 := by
    simpa [prefixWord, tailWord_3643529, baseEnd_3643529] using wordTrace_append hprefix tailTrace_3643529
  have hstable : (prefixWord ++ tailWord_3643529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643529).length < 2 ^ (prefixWord ++ tailWord_3643529).sum := by decide
  have hdescent : baseEnd_3643529 < baseStart_3643529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643539 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 4, 5, 2]
def baseStart_3643539 : Nat := 118140960795 + 3643539 * 2 ^ 59
def prefixEnd_3643539 : Nat := 4983230072969 + 3 ^ 40 * 3643539 * 2
def baseEnd_3643539 : Nat := 1870886790402125370606175

theorem tailTrace_3643539 : CollatzResearch.WordTrace tailWord_3643539 prefixEnd_3643539 1870886790402125370606175 := by
  unfold tailWord_3643539
  simp only [CollatzResearch.WordTrace]
  refine ⟨132890784747087944765109671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88593856498058629843406447 132890784747087944765109671)
  ·
    refine ⟨199336177120631917147664507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132890784747087944765109671 199336177120631917147664507)
    ·
      refine ⟨299004265680947875721496761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199336177120631917147664507 299004265680947875721496761)
      ·
        refine ⟨224253199260710906791122571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299004265680947875721496761 224253199260710906791122571)
        ·
          refine ⟨336379798891066360186683857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224253199260710906791122571 336379798891066360186683857)
          ·
            refine ⟨252284849168299770140012893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336379798891066360186683857 252284849168299770140012893)
            ·
              refine ⟨94606818438112413802504835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252284849168299770140012893 94606818438112413802504835)
              ·
                refine ⟨141910227657168620703757253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94606818438112413802504835 141910227657168620703757253)
                ·
                  refine ⟨26608167685719116381954485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141910227657168620703757253 26608167685719116381954485)
                  ·
                    refine ⟨2494515720536167160808233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26608167685719116381954485 2494515720536167160808233)
                    ·
                      refine ⟨1870886790402125370606175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494515720536167160808233 1870886790402125370606175)
                      ·
                        rfl

theorem cell23_3643539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 5, 2].length) (baseStart_3643539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643539 prefixEnd_3643539 := by exact prefixLift 3643539
  have htrace : WordTrace (prefixWord ++ tailWord_3643539) baseStart_3643539 baseEnd_3643539 := by
    simpa [prefixWord, tailWord_3643539, baseEnd_3643539] using wordTrace_append hprefix tailTrace_3643539
  have hstable : (prefixWord ++ tailWord_3643539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643539).length < 2 ^ (prefixWord ++ tailWord_3643539).sum := by decide
  have hdescent : baseEnd_3643539 < baseStart_3643539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643549 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_3643549 : Nat := 118140960795 + 3643549 * 2 ^ 59
def prefixEnd_3643549 : Nat := 4983230072969 + 3 ^ 40 * 3643549 * 2
def baseEnd_3643549 : Nat := 623630641736223443827043

theorem tailTrace_3643549 : CollatzResearch.WordTrace tailWord_3643549 prefixEnd_3643549 623630641736223443827043 := by
  unfold tailWord_3643549
  simp only [CollatzResearch.WordTrace]
  refine ⟨132891149477051716472973701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88594099651367810981982467 132891149477051716472973701)
  ·
    refine ⟨24917090526947196838682569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132891149477051716472973701 24917090526947196838682569)
    ·
      refine ⟨18687817895210397629011927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24917090526947196838682569 18687817895210397629011927)
      ·
        refine ⟨28031726842815596443517891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18687817895210397629011927 28031726842815596443517891)
        ·
          refine ⟨42047590264223394665276837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28031726842815596443517891 42047590264223394665276837)
          ·
            refine ⟨7883923174541886499739407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42047590264223394665276837 7883923174541886499739407)
            ·
              refine ⟨11825884761812829749609111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7883923174541886499739407 11825884761812829749609111)
              ·
                refine ⟨17738827142719244624413667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11825884761812829749609111 17738827142719244624413667)
                ·
                  refine ⟨26608240714078866936620501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17738827142719244624413667 26608240714078866936620501)
                  ·
                    refine ⟨623630641736223443827043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26608240714078866936620501 623630641736223443827043)
                    ·
                      rfl

theorem cell23_3643549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_3643549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643549 prefixEnd_3643549 := by exact prefixLift 3643549
  have htrace : WordTrace (prefixWord ++ tailWord_3643549) baseStart_3643549 baseEnd_3643549 := by
    simpa [prefixWord, tailWord_3643549, baseEnd_3643549] using wordTrace_append hprefix tailTrace_3643549
  have hstable : (prefixWord ++ tailWord_3643549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643549).length < 2 ^ (prefixWord ++ tailWord_3643549).sum := by decide
  have hdescent : baseEnd_3643549 < baseStart_3643549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643589 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 1, 4, 3]
def baseStart_3643589 : Nat := 118140960795 + 3643589 * 2 ^ 59
def prefixEnd_3643589 : Nat := 4983230072969 + 3 ^ 40 * 3643589 * 2
def baseEnd_3643589 : Nat := 1870912464434850174980945

theorem tailTrace_3643589 : CollatzResearch.WordTrace tailWord_3643589 prefixEnd_3643589 1870912464434850174980945 := by
  unfold tailWord_3643589
  simp only [CollatzResearch.WordTrace]
  refine ⟨132892608396906803304429821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88595072264604535536286547 132892608396906803304429821)
  ·
    refine ⟨49834728148840051239161183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132892608396906803304429821 49834728148840051239161183)
    ·
      refine ⟨74752092223260076858741775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49834728148840051239161183 74752092223260076858741775)
      ·
        refine ⟨112128138334890115288112663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74752092223260076858741775 112128138334890115288112663)
        ·
          refine ⟨168192207502335172932168995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112128138334890115288112663 168192207502335172932168995)
          ·
            refine ⟨252288311253502759398253493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168192207502335172932168995 252288311253502759398253493)
            ·
              refine ⟨23652029180015883693586265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252288311253502759398253493 23652029180015883693586265)
              ·
                refine ⟨17739021885011912770189699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23652029180015883693586265 17739021885011912770189699)
                ·
                  refine ⟨26608532827517869155284549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17739021885011912770189699 26608532827517869155284549)
                  ·
                    refine ⟨4989099905159600466615853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26608532827517869155284549 4989099905159600466615853)
                    ·
                      refine ⟨1870912464434850174980945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4989099905159600466615853 1870912464434850174980945)
                      ·
                        rfl

theorem cell23_3643589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_3643589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643589 prefixEnd_3643589 := by exact prefixLift 3643589
  have htrace : WordTrace (prefixWord ++ tailWord_3643589) baseStart_3643589 baseEnd_3643589 := by
    simpa [prefixWord, tailWord_3643589, baseEnd_3643589] using wordTrace_append hprefix tailTrace_3643589
  have hstable : (prefixWord ++ tailWord_3643589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643589).length < 2 ^ (prefixWord ++ tailWord_3643589).sum := by decide
  have hdescent : baseEnd_3643589 < baseStart_3643589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643623 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3643623 : Nat := 118140960795 + 3643623 * 2 ^ 59
def prefixEnd_3643623 : Nat := 4983230072969 + 3 ^ 40 * 3643623 * 2
def baseEnd_3643623 : Nat := 1870929922777103041955789

theorem tailTrace_3643623 : CollatzResearch.WordTrace tailWord_3643623 prefixEnd_3643623 1870929922777103041955789 := by
  unfold tailWord_3643623
  simp only [CollatzResearch.WordTrace]
  refine ⟨132893848478783627111167523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88595898985855751407445015 132893848478783627111167523)
  ·
    refine ⟨199340772718175440666751285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132893848478783627111167523 199340772718175440666751285)
    ·
      refine ⟨18688197442328947562507933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199340772718175440666751285 18688197442328947562507933)
      ·
        refine ⟨7008074040873355335940475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18688197442328947562507933 7008074040873355335940475)
        ·
          refine ⟨10512111061310033003910713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008074040873355335940475 10512111061310033003910713)
          ·
            refine ⟨7884083295982524752933035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10512111061310033003910713 7884083295982524752933035)
            ·
              refine ⟨11826124943973787129399553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7884083295982524752933035 11826124943973787129399553)
              ·
                refine ⟨8869593707980340347049665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11826124943973787129399553 8869593707980340347049665)
                ·
                  refine ⟨6652195280985255260287249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8869593707980340347049665 6652195280985255260287249)
                  ·
                    refine ⟨4989146460738941445215437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6652195280985255260287249 4989146460738941445215437)
                    ·
                      refine ⟨1870929922777103041955789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4989146460738941445215437 1870929922777103041955789)
                      ·
                        rfl

theorem cell23_3643623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3643623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643623 prefixEnd_3643623 := by exact prefixLift 3643623
  have htrace : WordTrace (prefixWord ++ tailWord_3643623) baseStart_3643623 baseEnd_3643623 := by
    simpa [prefixWord, tailWord_3643623, baseEnd_3643623] using wordTrace_append hprefix tailTrace_3643623
  have hstable : (prefixWord ++ tailWord_3643623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643623).length < 2 ^ (prefixWord ++ tailWord_3643623).sum := by decide
  have hdescent : baseEnd_3643623 < baseStart_3643623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643656 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 3, 5]
def baseStart_3643656 : Nat := 118140960795 + 3643656 * 2 ^ 59
def prefixEnd_3643656 : Nat := 4983230072969 + 3 ^ 40 * 3643656 * 2
def baseEnd_3643656 : Nat := 623648955879567137614379

theorem tailTrace_3643656 : CollatzResearch.WordTrace tailWord_3643656 prefixEnd_3643656 623648955879567137614379 := by
  unfold tailWord_3643656
  simp only [CollatzResearch.WordTrace]
  refine ⟨66447526043832036873559411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88596701391776049164745881 66447526043832036873559411)
  ·
    refine ⟨99671289065748055310339117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66447526043832036873559411 99671289065748055310339117)
    ·
      refine ⟨37376733399655520741377169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99671289065748055310339117 37376733399655520741377169)
      ·
        refine ⟨28032550049741640556032877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37376733399655520741377169 28032550049741640556032877)
        ·
          refine ⟨10512206268653115208512329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28032550049741640556032877 10512206268653115208512329)
          ·
            refine ⟨7884154701489836406384247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10512206268653115208512329 7884154701489836406384247)
            ·
              refine ⟨11826232052234754609576371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7884154701489836406384247 11826232052234754609576371)
              ·
                refine ⟨17739348078352131914364557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11826232052234754609576371 17739348078352131914364557)
                ·
                  refine ⟨6652255529382049467886709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17739348078352131914364557 6652255529382049467886709)
                  ·
                    refine ⟨623648955879567137614379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6652255529382049467886709 623648955879567137614379)
                    ·
                      rfl

theorem cell23_3643656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_3643656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643656 prefixEnd_3643656 := by exact prefixLift 3643656
  have htrace : WordTrace (prefixWord ++ tailWord_3643656) baseStart_3643656 baseEnd_3643656 := by
    simpa [prefixWord, tailWord_3643656, baseEnd_3643656] using wordTrace_append hprefix tailTrace_3643656
  have hstable : (prefixWord ++ tailWord_3643656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643656).length < 2 ^ (prefixWord ++ tailWord_3643656).sum := by decide
  have hdescent : baseEnd_3643656 < baseStart_3643656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643669 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 3, 6]
def baseStart_3643669 : Nat := 118140960795 + 3643669 * 2 ^ 59
def prefixEnd_3643669 : Nat := 4983230072969 + 3 ^ 40 * 3643669 * 2
def baseEnd_3643669 : Nat := 623651180962403287326859

theorem tailTrace_3643669 : CollatzResearch.WordTrace tailWord_3643669 prefixEnd_3643669 623651180962403287326859 := by
  unfold tailWord_3643669
  simp only [CollatzResearch.WordTrace]
  refine ⟨132895526236616976967342061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88597017491077984644894707 132895526236616976967342061)
  ·
    refine ⟨49835822338731366362753273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132895526236616976967342061 49835822338731366362753273)
    ·
      refine ⟨37376866754048524772064955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49835822338731366362753273 37376866754048524772064955)
      ·
        refine ⟨56065300131072787158097433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37376866754048524772064955 56065300131072787158097433)
        ·
          refine ⟨42048975098304590368573075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56065300131072787158097433 42048975098304590368573075)
          ·
            refine ⟨63073462647456885552859613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42048975098304590368573075 63073462647456885552859613)
            ·
              refine ⟨23652548492796332082322355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63073462647456885552859613 23652548492796332082322355)
              ·
                refine ⟨35478822739194498123483533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23652548492796332082322355 35478822739194498123483533)
                ·
                  refine ⟨13304558527197936796306325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35478822739194498123483533 13304558527197936796306325)
                  ·
                    refine ⟨623651180962403287326859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13304558527197936796306325 623651180962403287326859)
                    ·
                      rfl

theorem cell23_3643669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_3643669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643669 prefixEnd_3643669 := by exact prefixLift 3643669
  have htrace : WordTrace (prefixWord ++ tailWord_3643669) baseStart_3643669 baseEnd_3643669 := by
    simpa [prefixWord, tailWord_3643669, baseEnd_3643669] using wordTrace_append hprefix tailTrace_3643669
  have hstable : (prefixWord ++ tailWord_3643669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643669).length < 2 ^ (prefixWord ++ tailWord_3643669).sum := by decide
  have hdescent : baseEnd_3643669 < baseStart_3643669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643706 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_3643706 : Nat := 118140960795 + 3643706 * 2 ^ 59
def prefixEnd_3643706 : Nat := 4983230072969 + 3 ^ 40 * 3643706 * 2
def baseEnd_3643706 : Nat := 1870972541671426217217907

theorem tailTrace_3643706 : CollatzResearch.WordTrace tailWord_3643706 prefixEnd_3643706 1870972541671426217217907 := by
  unfold tailWord_3643706
  simp only [CollatzResearch.WordTrace]
  refine ⟨33224218934370733071609743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88597917158321954857625981 33224218934370733071609743)
  ·
    refine ⟨49836328401556099607414615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33224218934370733071609743 49836328401556099607414615)
    ·
      refine ⟨74754492602334149411121923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49836328401556099607414615 74754492602334149411121923)
      ·
        refine ⟨112131738903501224116682885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74754492602334149411121923 112131738903501224116682885)
        ·
          refine ⟨21024701044406479521878041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112131738903501224116682885 21024701044406479521878041)
          ·
            refine ⟨15768525783304859641408531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21024701044406479521878041 15768525783304859641408531)
            ·
              refine ⟨23652788674957289462112797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15768525783304859641408531 23652788674957289462112797)
              ·
                refine ⟨8869795753108983548292299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23652788674957289462112797 8869795753108983548292299)
                ·
                  refine ⟨13304693629663475322438449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8869795753108983548292299 13304693629663475322438449)
                  ·
                    refine ⟨9978520222247606491828837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13304693629663475322438449 9978520222247606491828837)
                    ·
                      refine ⟨1870972541671426217217907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9978520222247606491828837 1870972541671426217217907)
                      ·
                        rfl

theorem cell23_3643706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_3643706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643706 prefixEnd_3643706 := by exact prefixLift 3643706
  have htrace : WordTrace (prefixWord ++ tailWord_3643706) baseStart_3643706 baseEnd_3643706 := by
    simpa [prefixWord, tailWord_3643706, baseEnd_3643706] using wordTrace_append hprefix tailTrace_3643706
  have hstable : (prefixWord ++ tailWord_3643706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643706).length < 2 ^ (prefixWord ++ tailWord_3643706).sum := by decide
  have hdescent : baseEnd_3643706 < baseStart_3643706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643710 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_3643710 : Nat := 118140960795 + 3643710 * 2 ^ 59
def prefixEnd_3643710 : Nat := 4983230072969 + 3 ^ 40 * 3643710 * 2
def baseEnd_3643710 : Nat := 1870974595594044201567889

theorem tailTrace_3643710 : CollatzResearch.WordTrace tailWord_3643710 prefixEnd_3643710 1870974595594044201567889 := by
  unfold tailWord_3643710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16612127703683555121198073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88598014419645627313056389 16612127703683555121198073)
  ·
    refine ⟨12459095777762666340898555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16612127703683555121198073 12459095777762666340898555)
    ·
      refine ⟨18688643666643999511347833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12459095777762666340898555 18688643666643999511347833)
      ·
        refine ⟨14016482749982999633510875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18688643666643999511347833 14016482749982999633510875)
        ·
          refine ⟨21024724124974499450266313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14016482749982999633510875 21024724124974499450266313)
          ·
            refine ⟨15768543093730874587699735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21024724124974499450266313 15768543093730874587699735)
            ·
              refine ⟨23652814640596311881549603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15768543093730874587699735 23652814640596311881549603)
              ·
                refine ⟨35479221960894467822324405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23652814640596311881549603 35479221960894467822324405)
                ·
                  refine ⟨3326177058833856358342913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35479221960894467822324405 3326177058833856358342913)
                  ·
                    refine ⟨2494632794125392268757185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3326177058833856358342913 2494632794125392268757185)
                    ·
                      refine ⟨1870974595594044201567889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494632794125392268757185 1870974595594044201567889)
                      ·
                        rfl

theorem cell23_3643710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_3643710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643710 prefixEnd_3643710 := by exact prefixLift 3643710
  have htrace : WordTrace (prefixWord ++ tailWord_3643710) baseStart_3643710 baseEnd_3643710 := by
    simpa [prefixWord, tailWord_3643710, baseEnd_3643710] using wordTrace_append hprefix tailTrace_3643710
  have hstable : (prefixWord ++ tailWord_3643710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643710).length < 2 ^ (prefixWord ++ tailWord_3643710).sum := by decide
  have hdescent : baseEnd_3643710 < baseStart_3643710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643726 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_3643726 : Nat := 118140960795 + 3643726 * 2 ^ 59
def prefixEnd_3643726 : Nat := 4983230072969 + 3 ^ 40 * 3643726 * 2
def baseEnd_3643726 : Nat := 1870982811284516138967815

theorem tailTrace_3643726 : CollatzResearch.WordTrace tailWord_3643726 prefixEnd_3643726 1870982811284516138967815 := by
  unfold tailWord_3643726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16612200649676309462770879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88598403464940317134778021 16612200649676309462770879)
  ·
    refine ⟨24918300974514464194156319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16612200649676309462770879 24918300974514464194156319)
    ·
      refine ⟨37377451461771696291234479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24918300974514464194156319 37377451461771696291234479)
      ·
        refine ⟨56066177192657544436851719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37377451461771696291234479 56066177192657544436851719)
        ·
          refine ⟨84099265788986316655277579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56066177192657544436851719 84099265788986316655277579)
          ·
            refine ⟨126148898683479474982916369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84099265788986316655277579 126148898683479474982916369)
            ·
              refine ⟨94611674012609606237187277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126148898683479474982916369 94611674012609606237187277)
              ·
                refine ⟨35479377754728602338945229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94611674012609606237187277 35479377754728602338945229)
                ·
                  refine ⟨13304766658023225877104461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35479377754728602338945229 13304766658023225877104461)
                  ·
                    refine ⟨4989287496758709703914173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13304766658023225877104461 4989287496758709703914173)
                    ·
                      refine ⟨1870982811284516138967815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4989287496758709703914173 1870982811284516138967815)
                      ·
                        rfl

theorem cell23_3643726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_3643726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643726 prefixEnd_3643726 := by exact prefixLift 3643726
  have htrace : WordTrace (prefixWord ++ tailWord_3643726) baseStart_3643726 baseEnd_3643726 := by
    simpa [prefixWord, tailWord_3643726, baseEnd_3643726] using wordTrace_append hprefix tailTrace_3643726
  have hstable : (prefixWord ++ tailWord_3643726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643726).length < 2 ^ (prefixWord ++ tailWord_3643726).sum := by decide
  have hdescent : baseEnd_3643726 < baseStart_3643726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643730 : List Nat := [3, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_3643730 : Nat := 118140960795 + 3643730 * 2 ^ 59
def prefixEnd_3643730 : Nat := 4983230072969 + 3 ^ 40 * 3643730 * 2
def baseEnd_3643730 : Nat := 1870984865207134123317797

theorem tailTrace_3643730 : CollatzResearch.WordTrace tailWord_3643730 prefixEnd_3643730 1870984865207134123317797 := by
  unfold tailWord_3643730
  simp only [CollatzResearch.WordTrace]
  refine ⟨33224437772348996096328161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88598500726263989590208429 33224437772348996096328161)
  ·
    refine ⟨24918328329261747072246121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33224437772348996096328161 24918328329261747072246121)
    ·
      refine ⟨18688746246946310304184591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24918328329261747072246121 18688746246946310304184591)
      ·
        refine ⟨28033119370419465456276887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18688746246946310304184591 28033119370419465456276887)
        ·
          refine ⟨42049679055629198184415331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28033119370419465456276887 42049679055629198184415331)
          ·
            refine ⟨63074518583443797276622997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42049679055629198184415331 63074518583443797276622997)
            ·
              refine ⟨2956618058598927997341703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63074518583443797276622997 2956618058598927997341703)
              ·
                refine ⟨4434927087898391996012555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956618058598927997341703 4434927087898391996012555)
                ·
                  refine ⟨6652390631847587994018833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4434927087898391996012555 6652390631847587994018833)
                  ·
                    refine ⟨4989292973885690995514125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6652390631847587994018833 4989292973885690995514125)
                    ·
                      refine ⟨1870984865207134123317797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4989292973885690995514125 1870984865207134123317797)
                      ·
                        rfl

theorem cell23_3643730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_3643730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643730 prefixEnd_3643730 := by exact prefixLift 3643730
  have htrace : WordTrace (prefixWord ++ tailWord_3643730) baseStart_3643730 baseEnd_3643730 := by
    simpa [prefixWord, tailWord_3643730, baseEnd_3643730] using wordTrace_append hprefix tailTrace_3643730
  have hstable : (prefixWord ++ tailWord_3643730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643730).length < 2 ^ (prefixWord ++ tailWord_3643730).sum := by decide
  have hdescent : baseEnd_3643730 < baseStart_3643730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643759 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 1, 8]
def baseStart_3643759 : Nat := 118140960795 + 3643759 * 2 ^ 59
def prefixEnd_3643759 : Nat := 4983230072969 + 3 ^ 40 * 3643759 * 2
def baseEnd_3643759 : Nat := 623666585382038169951721

theorem tailTrace_3643759 : CollatzResearch.WordTrace tailWord_3643759 prefixEnd_3643759 623666585382038169951721 := by
  unfold tailWord_3643759
  simp only [CollatzResearch.WordTrace]
  refine ⟨132898808806290922338118331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88599205870860614892078887 132898808806290922338118331)
  ·
    refine ⟨199348213209436383507177497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132898808806290922338118331 199348213209436383507177497)
    ·
      refine ⟨149511159907077287630383123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199348213209436383507177497 149511159907077287630383123)
      ·
        refine ⟨224266739860615931445574685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149511159907077287630383123 224266739860615931445574685)
        ·
          refine ⟨84100027447730974292090507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224266739860615931445574685 84100027447730974292090507)
          ·
            refine ⟨126150041171596461438135761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84100027447730974292090507 126150041171596461438135761)
            ·
              refine ⟨94612530878697346078601821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126150041171596461438135761 94612530878697346078601821)
              ·
                refine ⟨35479699079511504779475683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94612530878697346078601821 35479699079511504779475683)
                ·
                  refine ⟨53219548619267257169213525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35479699079511504779475683 53219548619267257169213525)
                  ·
                    refine ⟨623666585382038169951721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53219548619267257169213525 623666585382038169951721)
                    ·
                      rfl

theorem cell23_3643759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_3643759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643759 prefixEnd_3643759 := by exact prefixLift 3643759
  have htrace : WordTrace (prefixWord ++ tailWord_3643759) baseStart_3643759 baseEnd_3643759 := by
    simpa [prefixWord, tailWord_3643759, baseEnd_3643759] using wordTrace_append hprefix tailTrace_3643759
  have hstable : (prefixWord ++ tailWord_3643759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643759).length < 2 ^ (prefixWord ++ tailWord_3643759).sum := by decide
  have hdescent : baseEnd_3643759 < baseStart_3643759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643778 : List Nat := [3, 4, 2, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_3643778 : Nat := 118140960795 + 3643778 * 2 ^ 59
def prefixEnd_3643778 : Nat := 4983230072969 + 3 ^ 40 * 3643778 * 2
def baseEnd_3643778 : Nat := 1871009512278549935517577

theorem tailTrace_3643778 : CollatzResearch.WordTrace tailWord_3643778 prefixEnd_3643778 1871009512278549935517577 := by
  unfold tailWord_3643778
  simp only [CollatzResearch.WordTrace]
  refine ⟨33224875448305522145764997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88599667862148059055373325 33224875448305522145764997)
  ·
    refine ⟨6229664146557285402330937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33224875448305522145764997 6229664146557285402330937)
    ·
      refine ⟨4672248109917964051748203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6229664146557285402330937 4672248109917964051748203)
      ·
        refine ⟨7008372164876946077622305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4672248109917964051748203 7008372164876946077622305)
        ·
          refine ⟨5256279123657709558216729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7008372164876946077622305 5256279123657709558216729)
          ·
            refine ⟨3942209342743282168662547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5256279123657709558216729 3942209342743282168662547)
            ·
              refine ⟨5913314014114923252993821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942209342743282168662547 5913314014114923252993821)
              ·
                refine ⟨2217492755293096219872683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5913314014114923252993821 2217492755293096219872683)
                ·
                  refine ⟨3326239132939644329809025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217492755293096219872683 3326239132939644329809025)
                  ·
                    refine ⟨2494679349704733247356769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3326239132939644329809025 2494679349704733247356769)
                    ·
                      refine ⟨1871009512278549935517577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494679349704733247356769 1871009512278549935517577)
                      ·
                        rfl

theorem cell23_3643778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_3643778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643778 prefixEnd_3643778 := by exact prefixLift 3643778
  have htrace : WordTrace (prefixWord ++ tailWord_3643778) baseStart_3643778 baseEnd_3643778 := by
    simpa [prefixWord, tailWord_3643778, baseEnd_3643778] using wordTrace_append hprefix tailTrace_3643778
  have hstable : (prefixWord ++ tailWord_3643778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643778).length < 2 ^ (prefixWord ++ tailWord_3643778).sum := by decide
  have hdescent : baseEnd_3643778 < baseStart_3643778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643783 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 3, 4, 2]
def baseStart_3643783 : Nat := 118140960795 + 3643783 * 2 ^ 59
def prefixEnd_3643783 : Nat := 4983230072969 + 3 ^ 40 * 3643783 * 2
def baseEnd_3643783 : Nat := 1871012079681822415955053

theorem tailTrace_3643783 : CollatzResearch.WordTrace tailWord_3643783 prefixEnd_3643783 1871012079681822415955053 := by
  unfold tailWord_3643783
  simp only [CollatzResearch.WordTrace]
  refine ⟨132899684158203974436992003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88599789438802649624661335 132899684158203974436992003)
  ·
    refine ⟨199349526237305961655488005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132899684158203974436992003 199349526237305961655488005)
    ·
      refine ⟨37378036169494867810404001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199349526237305961655488005 37378036169494867810404001)
      ·
        refine ⟨28033527127121150857803001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37378036169494867810404001 28033527127121150857803001)
        ·
          refine ⟨21025145345340863143352251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28033527127121150857803001 21025145345340863143352251)
          ·
            refine ⟨31537718018011294715028377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21025145345340863143352251 31537718018011294715028377)
            ·
              refine ⟨23653288513508471036271283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31537718018011294715028377 23653288513508471036271283)
              ·
                refine ⟨35479932770262706554406925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23653288513508471036271283 35479932770262706554406925)
                ·
                  refine ⟨13304974788848514957902597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35479932770262706554406925 13304974788848514957902597)
                  ·
                    refine ⟨2494682772909096554606737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13304974788848514957902597 2494682772909096554606737)
                    ·
                      refine ⟨1871012079681822415955053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494682772909096554606737 1871012079681822415955053)
                      ·
                        rfl

theorem cell23_3643783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_3643783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643783 prefixEnd_3643783 := by exact prefixLift 3643783
  have htrace : WordTrace (prefixWord ++ tailWord_3643783) baseStart_3643783 baseEnd_3643783 := by
    simpa [prefixWord, tailWord_3643783, baseEnd_3643783] using wordTrace_append hprefix tailTrace_3643783
  have hstable : (prefixWord ++ tailWord_3643783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643783).length < 2 ^ (prefixWord ++ tailWord_3643783).sum := by decide
  have hdescent : baseEnd_3643783 < baseStart_3643783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643821 : List Nat := [1, 5, 2, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_3643821 : Nat := 118140960795 + 3643821 * 2 ^ 59
def prefixEnd_3643821 : Nat := 4983230072969 + 3 ^ 40 * 3643821 * 2
def baseEnd_3643821 : Nat := 1871031591946693267279879

theorem tailTrace_3643821 : CollatzResearch.WordTrace tailWord_3643821 prefixEnd_3643821 1871031591946693267279879 := by
  unfold tailWord_3643821
  simp only [CollatzResearch.WordTrace]
  refine ⟨132901070132066306926875317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88600713421377537951250211 132901070132066306926875317)
  ·
    refine ⟨12459475324881216274394561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132901070132066306926875317 12459475324881216274394561)
    ·
      refine ⟨9344606493660912205795921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12459475324881216274394561 9344606493660912205795921)
      ·
        refine ⟨7008454870245684154346941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9344606493660912205795921 7008454870245684154346941)
        ·
          refine ⟨2628170576342131557880103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7008454870245684154346941 2628170576342131557880103)
          ·
            refine ⟨3942255864513197336820155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628170576342131557880103 3942255864513197336820155)
            ·
              refine ⟨5913383796769796005230233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942255864513197336820155 5913383796769796005230233)
              ·
                refine ⟨4435037847577347003922675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5913383796769796005230233 4435037847577347003922675)
                ·
                  refine ⟨6652556771366020505884013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4435037847577347003922675 6652556771366020505884013)
                  ·
                    refine ⟨2494708789262257689706505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6652556771366020505884013 2494708789262257689706505)
                    ·
                      refine ⟨1871031591946693267279879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494708789262257689706505 1871031591946693267279879)
                      ·
                        rfl

theorem cell23_3643821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_3643821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643821 prefixEnd_3643821 := by exact prefixLift 3643821
  have htrace : WordTrace (prefixWord ++ tailWord_3643821) baseStart_3643821 baseEnd_3643821 := by
    simpa [prefixWord, tailWord_3643821, baseEnd_3643821] using wordTrace_append hprefix tailTrace_3643821
  have hstable : (prefixWord ++ tailWord_3643821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643821).length < 2 ^ (prefixWord ++ tailWord_3643821).sum := by decide
  have hdescent : baseEnd_3643821 < baseStart_3643821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643860 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_3643860 : Nat := 118140960795 + 3643860 * 2 ^ 59
def prefixEnd_3643860 : Nat := 4983230072969 + 3 ^ 40 * 3643860 * 2
def baseEnd_3643860 : Nat := 1871051617692218614692199

theorem tailTrace_3643860 : CollatzResearch.WordTrace tailWord_3643860 prefixEnd_3643860 1871051617692218614692199 := by
  unfold tailWord_3643860
  simp only [CollatzResearch.WordTrace]
  refine ⟨66451246289462508293772517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88601661719283344391696689 66451246289462508293772517)
  ·
    refine ⟨12459608679274220305082347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66451246289462508293772517 12459608679274220305082347)
    ·
      refine ⟨18689413018911330457623521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12459608679274220305082347 18689413018911330457623521)
      ·
        refine ⟨14017059764183497843217641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18689413018911330457623521 14017059764183497843217641)
        ·
          refine ⟨10512794823137623382413231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14017059764183497843217641 10512794823137623382413231)
          ·
            refine ⟨15769192234706435073619847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10512794823137623382413231 15769192234706435073619847)
            ·
              refine ⟨23653788352059652610429771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15769192234706435073619847 23653788352059652610429771)
              ·
                refine ⟨35480682528089478915644657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23653788352059652610429771 35480682528089478915644657)
                ·
                  refine ⟨26610511896067109186733493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35480682528089478915644657 26610511896067109186733493)
                  ·
                    refine ⟨2494735490256291486256265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26610511896067109186733493 2494735490256291486256265)
                    ·
                      refine ⟨1871051617692218614692199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494735490256291486256265 1871051617692218614692199)
                      ·
                        rfl

theorem cell23_3643860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_3643860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643860 prefixEnd_3643860 := by exact prefixLift 3643860
  have htrace : WordTrace (prefixWord ++ tailWord_3643860) baseStart_3643860 baseEnd_3643860 := by
    simpa [prefixWord, tailWord_3643860, baseEnd_3643860] using wordTrace_append hprefix tailTrace_3643860
  have hstable : (prefixWord ++ tailWord_3643860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643860).length < 2 ^ (prefixWord ++ tailWord_3643860).sum := by decide
  have hdescent : baseEnd_3643860 < baseStart_3643860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643883 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 3, 4]
def baseStart_3643883 : Nat := 118140960795 + 3643883 * 2 ^ 59
def prefixEnd_3643883 : Nat := 4983230072969 + 3 ^ 40 * 3643883 * 2
def baseEnd_3643883 : Nat := 623687809249090674901531

theorem tailTrace_3643883 : CollatzResearch.WordTrace tailWord_3643883 prefixEnd_3643883 623687809249090674901531 := by
  unfold tailWord_3643883
  simp only [CollatzResearch.WordTrace]
  refine ⟨132903331457841691515632303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88602220971894461010421535 132903331457841691515632303)
  ·
    refine ⟨199354997186762537273448455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132903331457841691515632303 199354997186762537273448455)
    ·
      refine ⟨299032495780143805910172683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199354997186762537273448455 299032495780143805910172683)
      ·
        refine ⟨448548743670215708865259025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299032495780143805910172683 448548743670215708865259025)
        ·
          refine ⟨336411557752661781648944269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448548743670215708865259025 336411557752661781648944269)
          ·
            refine ⟨126154334157248168118354101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 336411557752661781648944269 126154334157248168118354101)
            ·
              refine ⟨11826968827242015761095697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126154334157248168118354101 11826968827242015761095697)
              ·
                refine ⟨8870226620431511820821773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11826968827242015761095697 8870226620431511820821773)
                ·
                  refine ⟨3326334982661816932808165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8870226620431511820821773 3326334982661816932808165)
                  ·
                    refine ⟨623687809249090674901531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3326334982661816932808165 623687809249090674901531)
                    ·
                      rfl

theorem cell23_3643883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 4].length) (baseStart_3643883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643883 prefixEnd_3643883 := by exact prefixLift 3643883
  have htrace : WordTrace (prefixWord ++ tailWord_3643883) baseStart_3643883 baseEnd_3643883 := by
    simpa [prefixWord, tailWord_3643883, baseEnd_3643883] using wordTrace_append hprefix tailTrace_3643883
  have hstable : (prefixWord ++ tailWord_3643883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643883).length < 2 ^ (prefixWord ++ tailWord_3643883).sum := by decide
  have hdescent : baseEnd_3643883 < baseStart_3643883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643890 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_3643890 : Nat := 118140960795 + 3643890 * 2 ^ 59
def prefixEnd_3643890 : Nat := 4983230072969 + 3 ^ 40 * 3643890 * 2
def baseEnd_3643890 : Nat := 1871067022111853497317061

theorem tailTrace_3643890 : CollatzResearch.WordTrace tailWord_3643890 prefixEnd_3643890 1871067022111853497317061 := by
  unfold tailWord_3643890
  simp only [CollatzResearch.WordTrace]
  refine ⟨33225896692204082927784281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88602391179210887807424749 33225896692204082927784281)
  ·
    refine ⟨24919422519153062195838211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33225896692204082927784281 24919422519153062195838211)
    ·
      refine ⟨37379133778729593293757317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24919422519153062195838211 37379133778729593293757317)
      ·
        refine ⟨7008587583511798742579497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37379133778729593293757317 7008587583511798742579497)
        ·
          refine ⟨5256440687633849056934623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7008587583511798742579497 5256440687633849056934623)
          ·
            refine ⟨7884661031450773585401935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5256440687633849056934623 7884661031450773585401935)
            ·
              refine ⟨11826991547176160378102903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7884661031450773585401935 11826991547176160378102903)
              ·
                refine ⟨17740487320764240567154355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11826991547176160378102903 17740487320764240567154355)
                ·
                  refine ⟨26610730981146360850731533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17740487320764240567154355 26610730981146360850731533)
                  ·
                    refine ⟨9979024117929885319024325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26610730981146360850731533 9979024117929885319024325)
                    ·
                      refine ⟨1871067022111853497317061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9979024117929885319024325 1871067022111853497317061)
                      ·
                        rfl

theorem cell23_3643890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_3643890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643890 prefixEnd_3643890 := by exact prefixLift 3643890
  have htrace : WordTrace (prefixWord ++ tailWord_3643890) baseStart_3643890 baseEnd_3643890 := by
    simpa [prefixWord, tailWord_3643890, baseEnd_3643890] using wordTrace_append hprefix tailTrace_3643890
  have hstable : (prefixWord ++ tailWord_3643890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643890).length < 2 ^ (prefixWord ++ tailWord_3643890).sum := by decide
  have hdescent : baseEnd_3643890 < baseStart_3643890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643896 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 8]
def baseStart_3643896 : Nat := 118140960795 + 3643896 * 2 ^ 59
def prefixEnd_3643896 : Nat := 4983230072969 + 3 ^ 40 * 3643896 * 2
def baseEnd_3643896 : Nat := 207896678110642274871337

theorem tailTrace_3643896 : CollatzResearch.WordTrace tailWord_3643896 prefixEnd_3643896 207896678110642274871337 := by
  unfold tailWord_3643896
  simp only [CollatzResearch.WordTrace]
  refine ⟨66451902803397297367927771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88602537071196396490570361 66451902803397297367927771)
  ·
    refine ⟨99677854205095946051891657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66451902803397297367927771 99677854205095946051891657)
    ·
      refine ⟨74758390653821959538918743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99677854205095946051891657 74758390653821959538918743)
      ·
        refine ⟨112137585980732939308378115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74758390653821959538918743 112137585980732939308378115)
        ·
          refine ⟨168206378971099408962567173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112137585980732939308378115 168206378971099408962567173)
          ·
            refine ⟨31538696057081139180481345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168206378971099408962567173 31538696057081139180481345)
            ·
              refine ⟨23654022042810854385361009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31538696057081139180481345 23654022042810854385361009)
              ·
                refine ⟨17740516532108140789020757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23654022042810854385361009 17740516532108140789020757)
                ·
                  refine ⟨207896678110642274871337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17740516532108140789020757 207896678110642274871337)
                  ·
                    rfl

theorem cell23_3643896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 8].length) (baseStart_3643896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643896 prefixEnd_3643896 := by exact prefixLift 3643896
  have htrace : WordTrace (prefixWord ++ tailWord_3643896) baseStart_3643896 baseEnd_3643896 := by
    simpa [prefixWord, tailWord_3643896, baseEnd_3643896] using wordTrace_append hprefix tailTrace_3643896
  have hstable : (prefixWord ++ tailWord_3643896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643896).length < 2 ^ (prefixWord ++ tailWord_3643896).sum := by decide
  have hdescent : baseEnd_3643896 < baseStart_3643896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3643983 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 5]
def baseStart_3643983 : Nat := 118140960795 + 3643983 * 2 ^ 59
def prefixEnd_3643983 : Nat := 4983230072969 + 3 ^ 40 * 3643983 * 2
def baseEnd_3643983 : Nat := 1871114775812721633454133

theorem tailTrace_3643983 : CollatzResearch.WordTrace tailWord_3643983 prefixEnd_3643983 1871114775812721633454133 := by
  unfold tailWord_3643983
  simp only [CollatzResearch.WordTrace]
  refine ⟨132906978757479408594272603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88604652504986272396181735 132906978757479408594272603)
  ·
    refine ⟨199360468136219112891408905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132906978757479408594272603 199360468136219112891408905)
    ·
      refine ⟨149520351102164334668556679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199360468136219112891408905 149520351102164334668556679)
      ·
        refine ⟨224280526653246502002835019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149520351102164334668556679 224280526653246502002835019)
        ·
          refine ⟨336420789979869753004252529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224280526653246502002835019 336420789979869753004252529)
          ·
            refine ⟨252315592484902314753189397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336420789979869753004252529 252315592484902314753189397)
            ·
              refine ⟨11827293397729796004055753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 252315592484902314753189397 11827293397729796004055753)
              ·
                refine ⟨8870470048297347003041815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11827293397729796004055753 8870470048297347003041815)
                ·
                  refine ⟨13305705072446020504562723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8870470048297347003041815 13305705072446020504562723)
                  ·
                    refine ⟨19958557608669030756844085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13305705072446020504562723 19958557608669030756844085)
                    ·
                      refine ⟨1871114775812721633454133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19958557608669030756844085 1871114775812721633454133)
                      ·
                        rfl

theorem cell23_3643983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_3643983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3643983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3643983 prefixEnd_3643983 := by exact prefixLift 3643983
  have htrace : WordTrace (prefixWord ++ tailWord_3643983) baseStart_3643983 baseEnd_3643983 := by
    simpa [prefixWord, tailWord_3643983, baseEnd_3643983] using wordTrace_append hprefix tailTrace_3643983
  have hstable : (prefixWord ++ tailWord_3643983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3643983).length < 2 ^ (prefixWord ++ tailWord_3643983).sum := by decide
  have hdescent : baseEnd_3643983 < baseStart_3643983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3643983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644010 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_3644010 : Nat := 118140960795 + 3644010 * 2 ^ 59
def prefixEnd_3644010 : Nat := 4983230072969 + 3 ^ 40 * 3644010 * 2
def baseEnd_3644010 : Nat := 1871128639790393027816509

theorem tailTrace_3644010 : CollatzResearch.WordTrace tailWord_3644010 prefixEnd_3644010 1871128639790393027816509 := by
  unfold tailWord_3644010
  simp only [CollatzResearch.WordTrace]
  refine ⟨33226990882095398051376371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88605309018921061470336989 33226990882095398051376371)
  ·
    refine ⟨49840486323143097077064557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33226990882095398051376371 49840486323143097077064557)
    ·
      refine ⟨18690182371178661403899209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49840486323143097077064557 18690182371178661403899209)
      ·
        refine ⟨14017636778383996052924407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18690182371178661403899209 14017636778383996052924407)
        ·
          refine ⟨21026455167575994079386611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14017636778383996052924407 21026455167575994079386611)
          ·
            refine ⟨31539682751363991119079917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21026455167575994079386611 31539682751363991119079917)
            ·
              refine ⟨11827381031761496669654969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31539682751363991119079917 11827381031761496669654969)
              ·
                refine ⟨8870535773821122502241227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11827381031761496669654969 8870535773821122502241227)
                ·
                  refine ⟨13305803660731683753361841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8870535773821122502241227 13305803660731683753361841)
                  ·
                    refine ⟨9979352745548762815021381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13305803660731683753361841 9979352745548762815021381)
                    ·
                      refine ⟨1871128639790393027816509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9979352745548762815021381 1871128639790393027816509)
                      ·
                        rfl

theorem cell23_3644010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_3644010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644010 prefixEnd_3644010 := by exact prefixLift 3644010
  have htrace : WordTrace (prefixWord ++ tailWord_3644010) baseStart_3644010 baseEnd_3644010 := by
    simpa [prefixWord, tailWord_3644010, baseEnd_3644010] using wordTrace_append hprefix tailTrace_3644010
  have hstable : (prefixWord ++ tailWord_3644010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644010).length < 2 ^ (prefixWord ++ tailWord_3644010).sum := by decide
  have hdescent : baseEnd_3644010 < baseStart_3644010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644014 : List Nat := [4, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_3644014 : Nat := 118140960795 + 3644014 * 2 ^ 59
def prefixEnd_3644014 : Nat := 4983230072969 + 3 ^ 40 * 3644014 * 2
def baseEnd_3644014 : Nat := 1871130693713011012166491

theorem tailTrace_3644014 : CollatzResearch.WordTrace tailWord_3644014 prefixEnd_3644014 1871130693713011012166491 := by
  unfold tailWord_3644014
  simp only [CollatzResearch.WordTrace]
  refine ⟨16613513677545887611081387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88605406280244733925767397 16613513677545887611081387)
  ·
    refine ⟨24920270516318831416622081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16613513677545887611081387 24920270516318831416622081)
    ·
      refine ⟨18690202887239123562466561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24920270516318831416622081 18690202887239123562466561)
      ·
        refine ⟨14017652165429342671849921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18690202887239123562466561 14017652165429342671849921)
        ·
          refine ⟨10513239124072007003887441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14017652165429342671849921 10513239124072007003887441)
          ·
            refine ⟨7884929343054005252915581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10513239124072007003887441 7884929343054005252915581)
            ·
              refine ⟨2956848503645251969843343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7884929343054005252915581 2956848503645251969843343)
              ·
                refine ⟨4435272755467877954765015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956848503645251969843343 4435272755467877954765015)
                ·
                  refine ⟨6652909133201816932147523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4435272755467877954765015 6652909133201816932147523)
                  ·
                    refine ⟨9979363699802725398221285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6652909133201816932147523 9979363699802725398221285)
                    ·
                      refine ⟨1871130693713011012166491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9979363699802725398221285 1871130693713011012166491)
                      ·
                        rfl

theorem cell23_3644014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_3644014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644014 prefixEnd_3644014 := by exact prefixLift 3644014
  have htrace : WordTrace (prefixWord ++ tailWord_3644014) baseStart_3644014 baseEnd_3644014 := by
    simpa [prefixWord, tailWord_3644014, baseEnd_3644014] using wordTrace_append hprefix tailTrace_3644014
  have hstable : (prefixWord ++ tailWord_3644014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644014).length < 2 ^ (prefixWord ++ tailWord_3644014).sum := by decide
  have hdescent : baseEnd_3644014 < baseStart_3644014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644033 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3644033 : Nat := 118140960795 + 3644033 * 2 ^ 59
def prefixEnd_3644033 : Nat := 4983230072969 + 3 ^ 40 * 3644033 * 2
def baseEnd_3644033 : Nat := 623713483281815479276301

theorem tailTrace_3644033 : CollatzResearch.WordTrace tailWord_3644033 prefixEnd_3644033 623713483281815479276301 := by
  unfold tailWord_3644033
  simp only [CollatzResearch.WordTrace]
  refine ⟨132908802407298267133592753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88605868271532178089061835 132908802407298267133592753)
  ·
    refine ⟨99681601805473700350194565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132908802407298267133592753 99681601805473700350194565)
    ·
      refine ⟨18690300338526318815661481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99681601805473700350194565 18690300338526318815661481)
      ·
        refine ⟨14017725253894739111746111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18690300338526318815661481 14017725253894739111746111)
        ·
          refine ⟨21026587880842108667619167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14017725253894739111746111 21026587880842108667619167)
          ·
            refine ⟨31539881821263163001428751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21026587880842108667619167 31539881821263163001428751)
            ·
              refine ⟨47309822731894744502143127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31539881821263163001428751 47309822731894744502143127)
              ·
                refine ⟨70964734097842116753214691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47309822731894744502143127 70964734097842116753214691)
                ·
                  refine ⟨106447101146763175129822037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70964734097842116753214691 106447101146763175129822037)
                  ·
                    refine ⟨623713483281815479276301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 106447101146763175129822037 623713483281815479276301)
                    ·
                      rfl

theorem cell23_3644033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3644033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644033 prefixEnd_3644033 := by exact prefixLift 3644033
  have htrace : WordTrace (prefixWord ++ tailWord_3644033) baseStart_3644033 baseEnd_3644033 := by
    simpa [prefixWord, tailWord_3644033, baseEnd_3644033] using wordTrace_append hprefix tailTrace_3644033
  have hstable : (prefixWord ++ tailWord_3644033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644033).length < 2 ^ (prefixWord ++ tailWord_3644033).sum := by decide
  have hdescent : baseEnd_3644033 < baseStart_3644033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644057 : List Nat := [1, 2, 1, 2, 1, 2, 4, 4, 1, 3, 2]
def baseStart_3644057 : Nat := 118140960795 + 3644057 * 2 ^ 59
def prefixEnd_3644057 : Nat := 4983230072969 + 3 ^ 40 * 3644057 * 2
def baseEnd_3644057 : Nat := 1871152773381154343928793

theorem tailTrace_3644057 : CollatzResearch.WordTrace tailWord_3644057 prefixEnd_3644057 1871152773381154343928793 := by
  unfold tailWord_3644057
  simp only [CollatzResearch.WordTrace]
  refine ⟨132909677759211319232466425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88606451839474212821644283 132909677759211319232466425)
  ·
    refine ⟨99682258319408489424349819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132909677759211319232466425 99682258319408489424349819)
    ·
      refine ⟨149523387479112734136524729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99682258319408489424349819 149523387479112734136524729)
      ·
        refine ⟨112142540609334550602393547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149523387479112734136524729 112142540609334550602393547)
        ·
          refine ⟨168213810914001825903590321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112142540609334550602393547 168213810914001825903590321)
          ·
            refine ⟨126160358185501369427692741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168213810914001825903590321 126160358185501369427692741)
            ·
              refine ⟨23655067159781506767692389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126160358185501369427692741 23655067159781506767692389)
              ·
                refine ⟨4435325092459032518942323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23655067159781506767692389 4435325092459032518942323)
                ·
                  refine ⟨6652987638688548778413485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4435325092459032518942323 6652987638688548778413485)
                  ·
                    refine ⟨2494870364508205791905057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6652987638688548778413485 2494870364508205791905057)
                    ·
                      refine ⟨1871152773381154343928793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494870364508205791905057 1871152773381154343928793)
                      ·
                        rfl

theorem cell23_3644057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 3, 2].length) (baseStart_3644057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644057 prefixEnd_3644057 := by exact prefixLift 3644057
  have htrace : WordTrace (prefixWord ++ tailWord_3644057) baseStart_3644057 baseEnd_3644057 := by
    simpa [prefixWord, tailWord_3644057, baseEnd_3644057] using wordTrace_append hprefix tailTrace_3644057
  have hstable : (prefixWord ++ tailWord_3644057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644057).length < 2 ^ (prefixWord ++ tailWord_3644057).sum := by decide
  have hdescent : baseEnd_3644057 < baseStart_3644057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644104 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 1, 4, 2]
def baseStart_3644104 : Nat := 118140960795 + 3644104 * 2 ^ 59
def prefixEnd_3644104 : Nat := 4983230072969 + 3 ^ 40 * 3644104 * 2
def baseEnd_3644104 : Nat := 1871176906971915660041077

theorem tailTrace_3644104 : CollatzResearch.WordTrace tailWord_3644104 prefixEnd_3644104 1871176906971915660041077 := by
  unfold tailWord_3644104
  simp only [CollatzResearch.WordTrace]
  refine ⟨66455695995020523129713683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88607594660027364172951577 66455695995020523129713683)
  ·
    refine ⟨99683543992530784694570525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66455695995020523129713683 99683543992530784694570525)
    ·
      refine ⟨37381328997199044260463947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99683543992530784694570525 37381328997199044260463947)
      ·
        refine ⟨56071993495798566390695921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37381328997199044260463947 56071993495798566390695921)
        ·
          refine ⟨42053995121848924793021941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56071993495798566390695921 42053995121848924793021941)
          ·
            refine ⟨3942562042673336699345807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42053995121848924793021941 3942562042673336699345807)
            ·
              refine ⟨5913843064010005049018711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942562042673336699345807 5913843064010005049018711)
              ·
                refine ⟨8870764596015007573528067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5913843064010005049018711 8870764596015007573528067)
                ·
                  refine ⟨13306146894022511360292101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8870764596015007573528067 13306146894022511360292101)
                  ·
                    refine ⟨2494902542629220880054769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13306146894022511360292101 2494902542629220880054769)
                    ·
                      refine ⟨1871176906971915660041077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2494902542629220880054769 1871176906971915660041077)
                      ·
                        rfl

theorem cell23_3644104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_3644104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644104 prefixEnd_3644104 := by exact prefixLift 3644104
  have htrace : WordTrace (prefixWord ++ tailWord_3644104) baseStart_3644104 baseEnd_3644104 := by
    simpa [prefixWord, tailWord_3644104, baseEnd_3644104] using wordTrace_append hprefix tailTrace_3644104
  have hstable : (prefixWord ++ tailWord_3644104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644104).length < 2 ^ (prefixWord ++ tailWord_3644104).sum := by decide
  have hdescent : baseEnd_3644104 < baseStart_3644104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644110 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 7]
def baseStart_3644110 : Nat := 118140960795 + 3644110 * 2 ^ 59
def prefixEnd_3644110 : Nat := 4983230072969 + 3 ^ 40 * 3644110 * 2
def baseEnd_3644110 : Nat := 207908887539538070729561

theorem tailTrace_3644110 : CollatzResearch.WordTrace tailWord_3644110 prefixEnd_3644110 207908887539538070729561 := by
  unfold tailWord_3644110
  simp only [CollatzResearch.WordTrace]
  refine ⟨16613951353502413660518223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88607740552012872856097189 16613951353502413660518223)
  ·
    refine ⟨24920927030253620490777335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16613951353502413660518223 24920927030253620490777335)
    ·
      refine ⟨37381390545380430736166003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24920927030253620490777335 37381390545380430736166003)
      ·
        refine ⟨56072085818070646104249005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37381390545380430736166003 56072085818070646104249005)
        ·
          refine ⟨21027032181776492289093377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56072085818070646104249005 21027032181776492289093377)
          ·
            refine ⟨15770274136332369216820033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21027032181776492289093377 15770274136332369216820033)
            ·
              refine ⟨11827705602249276912615025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15770274136332369216820033 11827705602249276912615025)
              ·
                refine ⟨8870779201686957684461269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11827705602249276912615025 8870779201686957684461269)
                ·
                  refine ⟨207908887539538070729561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8870779201686957684461269 207908887539538070729561)
                  ·
                    rfl

theorem cell23_3644110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_3644110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644110 prefixEnd_3644110 := by exact prefixLift 3644110
  have htrace : WordTrace (prefixWord ++ tailWord_3644110) baseStart_3644110 baseEnd_3644110 := by
    simpa [prefixWord, tailWord_3644110, baseEnd_3644110] using wordTrace_append hprefix tailTrace_3644110
  have hstable : (prefixWord ++ tailWord_3644110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644110).length < 2 ^ (prefixWord ++ tailWord_3644110).sum := by decide
  have hdescent : baseEnd_3644110 < baseStart_3644110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644127 : List Nat := [1, 1, 2, 3, 2, 3, 3, 3, 5]
def baseStart_3644127 : Nat := 118140960795 + 3644127 * 2 ^ 59
def prefixEnd_3644127 : Nat := 4983230072969 + 3 ^ 40 * 3644127 * 2
def baseEnd_3644127 : Nat := 207909857447441007783719

theorem tailTrace_3644127 : CollatzResearch.WordTrace tailWord_3644127 prefixEnd_3644127 207909857447441007783719 := by
  unfold tailWord_3644127
  simp only [CollatzResearch.WordTrace]
  refine ⟨132912230868957721187514635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88608153912638480791676423 132912230868957721187514635)
  ·
    refine ⟨199368346303436581781271953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132912230868957721187514635 199368346303436581781271953)
    ·
      refine ⟨149526259727577436335953965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199368346303436581781271953 149526259727577436335953965)
      ·
        refine ⟨56072347397841538625982737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149526259727577436335953965 56072347397841538625982737)
        ·
          refine ⟨42054260548381153969487053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56072347397841538625982737 42054260548381153969487053)
          ·
            refine ⟨15770347705642932738557645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42054260548381153969487053 15770347705642932738557645)
            ·
              refine ⟨5913880389616099776959117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15770347705642932738557645 5913880389616099776959117)
              ·
                refine ⟨2217705146106037416359669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5913880389616099776959117 2217705146106037416359669)
                ·
                  refine ⟨207909857447441007783719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2217705146106037416359669 207909857447441007783719)
                  ·
                    rfl

theorem cell23_3644127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 5].length) (baseStart_3644127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644127 prefixEnd_3644127 := by exact prefixLift 3644127
  have htrace : WordTrace (prefixWord ++ tailWord_3644127) baseStart_3644127 baseEnd_3644127 := by
    simpa [prefixWord, tailWord_3644127, baseEnd_3644127] using wordTrace_append hprefix tailTrace_3644127
  have hstable : (prefixWord ++ tailWord_3644127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644127).length < 2 ^ (prefixWord ++ tailWord_3644127).sum := by decide
  have hdescent : baseEnd_3644127 < baseStart_3644127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644197 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 2, 2, 3]
def baseStart_3644197 : Nat := 118140960795 + 3644197 * 2 ^ 59
def prefixEnd_3644197 : Nat := 4983230072969 + 3 ^ 40 * 3644197 * 2
def baseEnd_3644197 : Nat := 1871224660672783796178149

theorem tailTrace_3644197 : CollatzResearch.WordTrace tailWord_3644197 prefixEnd_3644197 1871224660672783796178149 := by
  unfold tailWord_3644197
  simp only [CollatzResearch.WordTrace]
  refine ⟨132914783978704123142562845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88609855985802748761708563 132914783978704123142562845)
  ·
    refine ⟨49843043992014046178461067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132914783978704123142562845 49843043992014046178461067)
    ·
      refine ⟨74764565988021069267691601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49843043992014046178461067 74764565988021069267691601)
      ·
        refine ⟨56073424491015801950768701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74764565988021069267691601 56073424491015801950768701)
        ·
          refine ⟨21027534184130925731538263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56073424491015801950768701 21027534184130925731538263)
          ·
            refine ⟨31541301276196388597307395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21027534184130925731538263 31541301276196388597307395)
            ·
              refine ⟨47311951914294582895961093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31541301276196388597307395 47311951914294582895961093)
              ·
                refine ⟨8870990983930234292992705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47311951914294582895961093 8870990983930234292992705)
                ·
                  refine ⟨6653243237947675719744529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8870990983930234292992705 6653243237947675719744529)
                  ·
                    refine ⟨4989932428460756789808397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6653243237947675719744529 4989932428460756789808397)
                    ·
                      refine ⟨1871224660672783796178149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4989932428460756789808397 1871224660672783796178149)
                      ·
                        rfl

theorem cell23_3644197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_3644197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644197 prefixEnd_3644197 := by exact prefixLift 3644197
  have htrace : WordTrace (prefixWord ++ tailWord_3644197) baseStart_3644197 baseEnd_3644197 := by
    simpa [prefixWord, tailWord_3644197, baseEnd_3644197] using wordTrace_append hprefix tailTrace_3644197
  have hstable : (prefixWord ++ tailWord_3644197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644197).length < 2 ^ (prefixWord ++ tailWord_3644197).sum := by decide
  have hdescent : baseEnd_3644197 < baseStart_3644197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644204 : List Nat := [2, 2, 1, 1, 1, 4, 3, 4, 1, 4]
def baseStart_3644204 : Nat := 118140960795 + 3644204 * 2 ^ 59
def prefixEnd_3644204 : Nat := 4983230072969 + 3 ^ 40 * 3644204 * 2
def baseEnd_3644204 : Nat := 623742751679121756263539

theorem tailTrace_3644204 : CollatzResearch.WordTrace tailWord_3644204 prefixEnd_3644204 623742751679121756263539 := by
  unfold tailWord_3644204
  simp only [CollatzResearch.WordTrace]
  refine ⟨66457519644839381669033833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88610026193119175558711777 66457519644839381669033833)
  ·
    refine ⟨49843139733629536251775375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66457519644839381669033833 49843139733629536251775375)
    ·
      refine ⟨74764709600444304377663063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49843139733629536251775375 74764709600444304377663063)
      ·
        refine ⟨112147064400666456566494595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74764709600444304377663063 112147064400666456566494595)
        ·
          refine ⟨168220596600999684849741893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112147064400666456566494595 168220596600999684849741893)
          ·
            refine ⟨31541361862687440909326605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168220596600999684849741893 31541361862687440909326605)
            ·
              refine ⟨11828010698507790340997477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31541361862687440909326605 11828010698507790340997477)
              ·
                refine ⟨2217752005970210688937027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11828010698507790340997477 2217752005970210688937027)
                ·
                  refine ⟨3326628008955316033405541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217752005970210688937027 3326628008955316033405541)
                  ·
                    refine ⟨623742751679121756263539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3326628008955316033405541 623742751679121756263539)
                    ·
                      rfl

theorem cell23_3644204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_3644204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644204 prefixEnd_3644204 := by exact prefixLift 3644204
  have htrace : WordTrace (prefixWord ++ tailWord_3644204) baseStart_3644204 baseEnd_3644204 := by
    simpa [prefixWord, tailWord_3644204, baseEnd_3644204] using wordTrace_append hprefix tailTrace_3644204
  have hstable : (prefixWord ++ tailWord_3644204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644204).length < 2 ^ (prefixWord ++ tailWord_3644204).sum := by decide
  have hdescent : baseEnd_3644204 < baseStart_3644204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644228 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3644228 : Nat := 118140960795 + 3644228 * 2 ^ 59
def prefixEnd_3644228 : Nat := 4983230072969 + 3 ^ 40 * 3644228 * 2
def baseEnd_3644228 : Nat := 1871240578573073174890507

theorem tailTrace_3644228 : CollatzResearch.WordTrace tailWord_3644228 prefixEnd_3644228 1871240578573073174890507 := by
  unfold tailWord_3644228
  simp only [CollatzResearch.WordTrace]
  refine ⟨66457957320795907718470669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88610609761061210291294225 66457957320795907718470669)
  ·
    refine ⟨24921733995298465394426501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66457957320795907718470669 24921733995298465394426501)
    ·
      refine ⟨4672825124118462261454969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24921733995298465394426501 4672825124118462261454969)
      ·
        refine ⟨3504618843088846696091227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4672825124118462261454969 3504618843088846696091227)
        ·
          refine ⟨5256928264633270044136841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3504618843088846696091227 5256928264633270044136841)
          ·
            refine ⟨3942696198474952533102631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5256928264633270044136841 3942696198474952533102631)
            ·
              refine ⟨5914044297712428799653947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942696198474952533102631 5914044297712428799653947)
              ·
                refine ⟨8871066446568643199480921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5914044297712428799653947 8871066446568643199480921)
                ·
                  refine ⟨6653299834926482399610691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8871066446568643199480921 6653299834926482399610691)
                  ·
                    refine ⟨9979949752389723599416037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6653299834926482399610691 9979949752389723599416037)
                    ·
                      refine ⟨1871240578573073174890507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9979949752389723599416037 1871240578573073174890507)
                      ·
                        rfl

theorem cell23_3644228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3644228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644228 prefixEnd_3644228 := by exact prefixLift 3644228
  have htrace : WordTrace (prefixWord ++ tailWord_3644228) baseStart_3644228 baseEnd_3644228 := by
    simpa [prefixWord, tailWord_3644228, baseEnd_3644228] using wordTrace_append hprefix tailTrace_3644228
  have hstable : (prefixWord ++ tailWord_3644228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644228).length < 2 ^ (prefixWord ++ tailWord_3644228).sum := by decide
  have hdescent : baseEnd_3644228 < baseStart_3644228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644261 : List Nat := [1, 3, 1, 3, 1, 1, 4, 4, 1, 1, 3]
def baseStart_3644261 : Nat := 118140960795 + 3644261 * 2 ^ 59
def prefixEnd_3644261 : Nat := 4983230072969 + 3 ^ 40 * 3644261 * 2
def baseEnd_3644261 : Nat := 1871257523434671545777855

theorem tailTrace_3644261 : CollatzResearch.WordTrace tailWord_3644261 prefixEnd_3644261 1871257523434671545777855 := by
  unfold tailWord_3644261
  simp only [CollatzResearch.WordTrace]
  refine ⟨132917118250472262072892637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88611412166981508048595091 132917118250472262072892637)
  ·
    refine ⟨49843919343927098277334739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132917118250472262072892637 49843919343927098277334739)
    ·
      refine ⟨74765879015890647416002109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49843919343927098277334739 74765879015890647416002109)
      ·
        refine ⟨28037204630958992781000791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74765879015890647416002109 28037204630958992781000791)
        ·
          refine ⟨42055806946438489171501187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28037204630958992781000791 42055806946438489171501187)
          ·
            refine ⟨63083710419657733757251781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42055806946438489171501187 63083710419657733757251781)
            ·
              refine ⟨11828195703685825079484709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63083710419657733757251781 11828195703685825079484709)
              ·
                refine ⟨2217786694441092202403383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11828195703685825079484709 2217786694441092202403383)
                ·
                  refine ⟨3326680041661638303605075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2217786694441092202403383 3326680041661638303605075)
                  ·
                    refine ⟨4990020062492457455407613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3326680041661638303605075 4990020062492457455407613)
                    ·
                      refine ⟨1871257523434671545777855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4990020062492457455407613 1871257523434671545777855)
                      ·
                        rfl

theorem cell23_3644261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_3644261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644261 prefixEnd_3644261 := by exact prefixLift 3644261
  have htrace : WordTrace (prefixWord ++ tailWord_3644261) baseStart_3644261 baseEnd_3644261 := by
    simpa [prefixWord, tailWord_3644261, baseEnd_3644261] using wordTrace_append hprefix tailTrace_3644261
  have hstable : (prefixWord ++ tailWord_3644261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644261).length < 2 ^ (prefixWord ++ tailWord_3644261).sum := by decide
  have hdescent : baseEnd_3644261 < baseStart_3644261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644287 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 3]
def baseStart_3644287 : Nat := 118140960795 + 3644287 * 2 ^ 59
def prefixEnd_3644287 : Nat := 4983230072969 + 3 ^ 40 * 3644287 * 2
def baseEnd_3644287 : Nat := 1871270873931688444052735

theorem tailTrace_3644287 : CollatzResearch.WordTrace tailWord_3644287 prefixEnd_3644287 1871270873931688444052735 := by
  unfold tailWord_3644287
  simp only [CollatzResearch.WordTrace]
  refine ⟨132918066548378068513339115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88612044365585379008892743 132918066548378068513339115)
  ·
    refine ⟨199377099822567102770008673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132918066548378068513339115 199377099822567102770008673)
    ·
      refine ⟨149532824866925327077506505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199377099822567102770008673 149532824866925327077506505)
      ·
        refine ⟨112149618650193995308129879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149532824866925327077506505 112149618650193995308129879)
        ·
          refine ⟨168224427975290992962194819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112149618650193995308129879 168224427975290992962194819)
          ·
            refine ⟨252336641962936489443292229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168224427975290992962194819 252336641962936489443292229)
            ·
              refine ⟨47313120368050591770617293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252336641962936489443292229 47313120368050591770617293)
              ·
                refine ⟨17742420138018971913981485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47313120368050591770617293 17742420138018971913981485)
                ·
                  refine ⟨6653407551757114467743057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17742420138018971913981485 6653407551757114467743057)
                  ·
                    refine ⟨4990055663817835850807293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6653407551757114467743057 4990055663817835850807293)
                    ·
                      refine ⟨1871270873931688444052735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4990055663817835850807293 1871270873931688444052735)
                      ·
                        rfl

theorem cell23_3644287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_3644287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644287 prefixEnd_3644287 := by exact prefixLift 3644287
  have htrace : WordTrace (prefixWord ++ tailWord_3644287) baseStart_3644287 baseEnd_3644287 := by
    simpa [prefixWord, tailWord_3644287, baseEnd_3644287] using wordTrace_append hprefix tailTrace_3644287
  have hstable : (prefixWord ++ tailWord_3644287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644287).length < 2 ^ (prefixWord ++ tailWord_3644287).sum := by decide
  have hdescent : baseEnd_3644287 < baseStart_3644287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644358 : List Nat := [6, 1, 3, 1, 1, 11]
def baseStart_3644358 : Nat := 118140960795 + 3644358 * 2 ^ 59
def prefixEnd_3644358 : Nat := 4983230072969 + 3 ^ 40 * 3644358 * 2
def baseEnd_3644358 : Nat := 7700853214231101507263

theorem tailTrace_3644358 : CollatzResearch.WordTrace tailWord_3644358 prefixEnd_3644358 7700853214231101507263 := by
  unfold tailWord_3644358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4153770504097526488724179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88613770754080565092782485 4153770504097526488724179)
  ·
    refine ⟨6230655756146289733086269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4153770504097526488724179 6230655756146289733086269)
    ·
      refine ⟨2336495908554858649907351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6230655756146289733086269 2336495908554858649907351)
      ·
        refine ⟨3504743862832287974861027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2336495908554858649907351 3504743862832287974861027)
        ·
          refine ⟨5257115794248431962291541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3504743862832287974861027 5257115794248431962291541)
          ·
            refine ⟨7700853214231101507263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5257115794248431962291541 7700853214231101507263)
            ·
              rfl

theorem cell23_3644358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 11].length) (baseStart_3644358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644358 prefixEnd_3644358 := by exact prefixLift 3644358
  have htrace : WordTrace (prefixWord ++ tailWord_3644358) baseStart_3644358 baseEnd_3644358 := by
    simpa [prefixWord, tailWord_3644358, baseEnd_3644358] using wordTrace_append hprefix tailTrace_3644358
  have hstable : (prefixWord ++ tailWord_3644358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644358).length < 2 ^ (prefixWord ++ tailWord_3644358).sum := by decide
  have hdescent : baseEnd_3644358 < baseStart_3644358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644391 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_3644391 : Nat := 118140960795 + 3644391 * 2 ^ 59
def prefixEnd_3644391 : Nat := 4983230072969 + 3 ^ 40 * 3644391 * 2
def baseEnd_3644391 : Nat := 1871324275919756037152257

theorem tailTrace_3644391 : CollatzResearch.WordTrace tailWord_3644391 prefixEnd_3644391 1871324275919756037152257 := by
  unfold tailWord_3644391
  simp only [CollatzResearch.WordTrace]
  refine ⟨132921859740001294275125027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88614573160000862850083351 132921859740001294275125027)
  ·
    refine ⟨199382789610001941412687541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132921859740001294275125027 199382789610001941412687541)
    ·
      refine ⟨18692136525937682007439457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199382789610001941412687541 18692136525937682007439457)
      ·
        refine ⟨14019102394453261505579593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18692136525937682007439457 14019102394453261505579593)
        ·
          refine ⟨10514326795839946129184695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14019102394453261505579593 10514326795839946129184695)
          ·
            refine ⟨15771490193759919193777043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10514326795839946129184695 15771490193759919193777043)
            ·
              refine ⟨23657235290639878790665565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15771490193759919193777043 23657235290639878790665565)
              ·
                refine ⟨8871463233989954546499587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23657235290639878790665565 8871463233989954546499587)
                ·
                  refine ⟨13307194850984931819749381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8871463233989954546499587 13307194850984931819749381)
                  ·
                    refine ⟨2495099034559674716203009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13307194850984931819749381 2495099034559674716203009)
                    ·
                      refine ⟨1871324275919756037152257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2495099034559674716203009 1871324275919756037152257)
                      ·
                        rfl

theorem cell23_3644391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_3644391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644391 prefixEnd_3644391 := by exact prefixLift 3644391
  have htrace : WordTrace (prefixWord ++ tailWord_3644391) baseStart_3644391 baseEnd_3644391 := by
    simpa [prefixWord, tailWord_3644391, baseEnd_3644391] using wordTrace_append hprefix tailTrace_3644391
  have hstable : (prefixWord ++ tailWord_3644391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644391).length < 2 ^ (prefixWord ++ tailWord_3644391).sum := by decide
  have hdescent : baseEnd_3644391 < baseStart_3644391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644424 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_3644424 : Nat := 118140960795 + 3644424 * 2 ^ 59
def prefixEnd_3644424 : Nat := 4983230072969 + 3 ^ 40 * 3644424 * 2
def baseEnd_3644424 : Nat := 1871341220781354408039605

theorem tailTrace_3644424 : CollatzResearch.WordTrace tailWord_3644424 prefixEnd_3644424 1871341220781354408039605 := by
  unfold tailWord_3644424
  simp only [CollatzResearch.WordTrace]
  refine ⟨66461531674440870455538163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88615375565921160607384217 66461531674440870455538163)
  ·
    refine ⟨99692297511661305683307245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66461531674440870455538163 99692297511661305683307245)
    ·
      refine ⟨37384611566872989631240217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99692297511661305683307245 37384611566872989631240217)
      ·
        refine ⟨28038458675154742223430163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37384611566872989631240217 28038458675154742223430163)
        ·
          refine ⟨42057688012732113335145245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28038458675154742223430163 42057688012732113335145245)
          ·
            refine ⟨15771633004774542500679467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42057688012732113335145245 15771633004774542500679467)
            ·
              refine ⟨23657449507161813751019201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15771633004774542500679467 23657449507161813751019201)
              ·
                refine ⟨17743087130371360313264401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23657449507161813751019201 17743087130371360313264401)
                ·
                  refine ⟨13307315347778520234948301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17743087130371360313264401 13307315347778520234948301)
                  ·
                    refine ⟨4990243255416945088105613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13307315347778520234948301 4990243255416945088105613)
                    ·
                      refine ⟨1871341220781354408039605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4990243255416945088105613 1871341220781354408039605)
                      ·
                        rfl

theorem cell23_3644424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_3644424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644424 prefixEnd_3644424 := by exact prefixLift 3644424
  have htrace : WordTrace (prefixWord ++ tailWord_3644424) baseStart_3644424 baseEnd_3644424 := by
    simpa [prefixWord, tailWord_3644424, baseEnd_3644424] using wordTrace_append hprefix tailTrace_3644424
  have hstable : (prefixWord ++ tailWord_3644424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644424).length < 2 ^ (prefixWord ++ tailWord_3644424).sum := by decide
  have hdescent : baseEnd_3644424 < baseStart_3644424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644464 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 4]
def baseStart_3644464 : Nat := 118140960795 + 3644464 * 2 ^ 59
def prefixEnd_3644464 : Nat := 4983230072969 + 3 ^ 40 * 3644464 * 2
def baseEnd_3644464 : Nat := 1871361760007534251539421

theorem tailTrace_3644464 : CollatzResearch.WordTrace tailWord_3644464 prefixEnd_3644464 1871361760007534251539421 := by
  unfold tailWord_3644464
  simp only [CollatzResearch.WordTrace]
  refine ⟨66462261134368413871266223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88616348179157885161688297 66462261134368413871266223)
  ·
    refine ⟨99693391701552620806899335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66462261134368413871266223 99693391701552620806899335)
    ·
      refine ⟨149540087552328931210349003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99693391701552620806899335 149540087552328931210349003)
      ·
        refine ⟨224310131328493396815523505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149540087552328931210349003 224310131328493396815523505)
        ·
          refine ⟨168232598496370047611642629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224310131328493396815523505 168232598496370047611642629)
          ·
            refine ⟨31543612218069383927182993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168232598496370047611642629 31543612218069383927182993)
            ·
              refine ⟨23657709163552037945387245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31543612218069383927182993 23657709163552037945387245)
              ·
                refine ⟨8871640936332014229520217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23657709163552037945387245 8871640936332014229520217)
                ·
                  refine ⟨6653730702249010672140163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8871640936332014229520217 6653730702249010672140163)
                  ·
                    refine ⟨9980596053373516008210245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6653730702249010672140163 9980596053373516008210245)
                    ·
                      refine ⟨1871361760007534251539421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9980596053373516008210245 1871361760007534251539421)
                      ·
                        rfl

theorem cell23_3644464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_3644464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644464 prefixEnd_3644464 := by exact prefixLift 3644464
  have htrace : WordTrace (prefixWord ++ tailWord_3644464) baseStart_3644464 baseEnd_3644464 := by
    simpa [prefixWord, tailWord_3644464, baseEnd_3644464] using wordTrace_append hprefix tailTrace_3644464
  have hstable : (prefixWord ++ tailWord_3644464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644464).length < 2 ^ (prefixWord ++ tailWord_3644464).sum := by decide
  have hdescent : baseEnd_3644464 < baseStart_3644464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644467 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 5]
def baseStart_3644467 : Nat := 118140960795 + 3644467 * 2 ^ 59
def prefixEnd_3644467 : Nat := 4983230072969 + 3 ^ 40 * 3644467 * 2
def baseEnd_3644467 : Nat := 1871363300449497739801907

theorem tailTrace_3644467 : CollatzResearch.WordTrace tailWord_3644467 prefixEnd_3644467 1871363300449497739801907 := by
  unfold tailWord_3644467
  simp only [CollatzResearch.WordTrace]
  refine ⟨132924631687725959254891655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88616421125150639503261103 132924631687725959254891655)
  ·
    refine ⟨199386947531588938882337483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132924631687725959254891655 199386947531588938882337483)
    ·
      refine ⟨299080421297383408323506225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199386947531588938882337483 299080421297383408323506225)
      ·
        refine ⟨224310315973037556242629669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299080421297383408323506225 224310315973037556242629669)
        ·
          refine ⟨42058184244944541795493063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224310315973037556242629669 42058184244944541795493063)
          ·
            refine ⟨63087276367416812693239595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42058184244944541795493063 63087276367416812693239595)
            ·
              refine ⟨94630914551125219039859393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63087276367416812693239595 94630914551125219039859393)
              ·
                refine ⟨70973185913343914279894545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94630914551125219039859393 70973185913343914279894545)
                ·
                  refine ⟨53229889435007935709920909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70973185913343914279894545 53229889435007935709920909)
                  ·
                    refine ⟨19961208538127975891220341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53229889435007935709920909 19961208538127975891220341)
                    ·
                      refine ⟨1871363300449497739801907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19961208538127975891220341 1871363300449497739801907)
                      ·
                        rfl

theorem cell23_3644467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_3644467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644467 prefixEnd_3644467 := by exact prefixLift 3644467
  have htrace : WordTrace (prefixWord ++ tailWord_3644467) baseStart_3644467 baseEnd_3644467 := by
    simpa [prefixWord, tailWord_3644467, baseEnd_3644467] using wordTrace_append hprefix tailTrace_3644467
  have hstable : (prefixWord ++ tailWord_3644467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644467).length < 2 ^ (prefixWord ++ tailWord_3644467).sum := by decide
  have hdescent : baseEnd_3644467 < baseStart_3644467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644474 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 5, 4]
def baseStart_3644474 : Nat := 118140960795 + 3644474 * 2 ^ 59
def prefixEnd_3644474 : Nat := 4983230072969 + 3 ^ 40 * 3644474 * 2
def baseEnd_3644474 : Nat := 623788964938026404138125

theorem tailTrace_3644474 : CollatzResearch.WordTrace tailWord_3644474 prefixEnd_3644474 623788964938026404138125 := by
  unfold tailWord_3644474
  simp only [CollatzResearch.WordTrace]
  refine ⟨33231221749675149862599119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88616591332467066300264317 33231221749675149862599119)
  ·
    refine ⟨49846832624512724793898679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33231221749675149862599119 49846832624512724793898679)
    ·
      refine ⟨74770248936769087190848019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49846832624512724793898679 74770248936769087190848019)
      ·
        refine ⟨112155373405153630786272029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74770248936769087190848019 112155373405153630786272029)
        ·
          refine ⟨42058265026932611544852011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112155373405153630786272029 42058265026932611544852011)
          ·
            refine ⟨63087397540398917317278017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42058265026932611544852011 63087397540398917317278017)
            ·
              refine ⟨47315548155299187987958513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63087397540398917317278017 47315548155299187987958513)
              ·
                refine ⟨35486661116474390990968885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47315548155299187987958513 35486661116474390990968885)
                ·
                  refine ⟨3326874479669474155403333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35486661116474390990968885 3326874479669474155403333)
                  ·
                    refine ⟨623788964938026404138125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3326874479669474155403333 623788964938026404138125)
                    ·
                      rfl

theorem cell23_3644474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_3644474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644474 prefixEnd_3644474 := by exact prefixLift 3644474
  have htrace : WordTrace (prefixWord ++ tailWord_3644474) baseStart_3644474 baseEnd_3644474 := by
    simpa [prefixWord, tailWord_3644474, baseEnd_3644474] using wordTrace_append hprefix tailTrace_3644474
  have hstable : (prefixWord ++ tailWord_3644474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644474).length < 2 ^ (prefixWord ++ tailWord_3644474).sum := by decide
  have hdescent : baseEnd_3644474 < baseStart_3644474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644504 : List Nat := [2, 1, 2, 2, 1, 3, 3, 3, 6]
def baseStart_3644504 : Nat := 118140960795 + 3644504 * 2 ^ 59
def prefixEnd_3644504 : Nat := 4983230072969 + 3 ^ 40 * 3644504 * 2
def baseEnd_3644504 : Nat := 207931366581523788337693

theorem tailTrace_3644504 : CollatzResearch.WordTrace tailWord_3644504 prefixEnd_3644504 207931366581523788337693 := by
  unfold tailWord_3644504
  simp only [CollatzResearch.WordTrace]
  refine ⟨66462990594295957286994283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88617320792394609715992377 66462990594295957286994283)
  ·
    refine ⟨99694485891443935930491425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66462990594295957286994283 99694485891443935930491425)
    ·
      refine ⟨74770864418582951947868569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99694485891443935930491425 74770864418582951947868569)
      ·
        refine ⟨56078148313937213960901427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74770864418582951947868569 56078148313937213960901427)
        ·
          refine ⟨84117222470905820941352141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56078148313937213960901427 84117222470905820941352141)
          ·
            refine ⟨31543958426589682853007053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84117222470905820941352141 31543958426589682853007053)
            ·
              refine ⟨11828984409971131069877645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31543958426589682853007053 11828984409971131069877645)
              ·
                refine ⟨4435869153739174151204117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11828984409971131069877645 4435869153739174151204117)
                ·
                  refine ⟨207931366581523788337693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4435869153739174151204117 207931366581523788337693)
                  ·
                    rfl

theorem cell23_3644504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 6].length) (baseStart_3644504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644504 prefixEnd_3644504 := by exact prefixLift 3644504
  have htrace : WordTrace (prefixWord ++ tailWord_3644504) baseStart_3644504 baseEnd_3644504 := by
    simpa [prefixWord, tailWord_3644504, baseEnd_3644504] using wordTrace_append hprefix tailTrace_3644504
  have hstable : (prefixWord ++ tailWord_3644504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644504).length < 2 ^ (prefixWord ++ tailWord_3644504).sum := by decide
  have hdescent : baseEnd_3644504 < baseStart_3644504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644594 : List Nat := [3, 2, 1, 1, 1, 5, 10]
def baseStart_3644594 : Nat := 118140960795 + 3644594 * 2 ^ 59
def prefixEnd_3644594 : Nat := 4983230072969 + 3 ^ 40 * 3644594 * 2
def baseEnd_3644594 : Nat := 23104055709785416579183

theorem tailTrace_3644594 : CollatzResearch.WordTrace tailWord_3644594 prefixEnd_3644594 23104055709785416579183 := by
  unfold tailWord_3644594
  simp only [CollatzResearch.WordTrace]
  refine ⟨33232315939566464986191209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88619509172177239963176557 33232315939566464986191209)
  ·
    refine ⟨24924236954674848739643407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33232315939566464986191209 24924236954674848739643407)
    ·
      refine ⟨37386355432012273109465111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24924236954674848739643407 37386355432012273109465111)
      ·
        refine ⟨56079533148018409664197667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37386355432012273109465111 56079533148018409664197667)
        ·
          refine ⟨84119299722027614496296501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56079533148018409664197667 84119299722027614496296501)
          ·
            refine ⟨7886184348940088859027797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84119299722027614496296501 7886184348940088859027797)
            ·
              refine ⟨23104055709785416579183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7886184348940088859027797 23104055709785416579183)
              ·
                rfl

theorem cell23_3644594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 10].length) (baseStart_3644594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644594 prefixEnd_3644594 := by exact prefixLift 3644594
  have htrace : WordTrace (prefixWord ++ tailWord_3644594) baseStart_3644594 baseEnd_3644594 := by
    simpa [prefixWord, tailWord_3644594, baseEnd_3644594] using wordTrace_append hprefix tailTrace_3644594
  have hstable : (prefixWord ++ tailWord_3644594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644594).length < 2 ^ (prefixWord ++ tailWord_3644594).sum := by decide
  have hdescent : baseEnd_3644594 < baseStart_3644594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644618 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_3644618 : Nat := 118140960795 + 3644618 * 2 ^ 59
def prefixEnd_3644618 : Nat := 4983230072969 + 3 ^ 40 * 3644618 * 2
def baseEnd_3644618 : Nat := 1871440836028326649013713

theorem tailTrace_3644618 : CollatzResearch.WordTrace tailWord_3644618 prefixEnd_3644618 1871440836028326649013713 := by
  unfold tailWord_3644618
  simp only [CollatzResearch.WordTrace]
  refine ⟨33232534777544728010909627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88620092740119274695759005 33232534777544728010909627)
  ·
    refine ⟨49848802166317092016364441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33232534777544728010909627 49848802166317092016364441)
    ·
      refine ⟨37386601624737819012273331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49848802166317092016364441 37386601624737819012273331)
      ·
        refine ⟨56079902437106728518409997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37386601624737819012273331 56079902437106728518409997)
        ·
          refine ⟨21029963413915023194403749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56079902437106728518409997 21029963413915023194403749)
          ·
            refine ⟨3943118140109066848950703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21029963413915023194403749 3943118140109066848950703)
            ·
              refine ⟨5914677210163600273426055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3943118140109066848950703 5914677210163600273426055)
              ·
                refine ⟨8872015815245400410139083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5914677210163600273426055 8872015815245400410139083)
                ·
                  refine ⟨13308023722868100615208625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8872015815245400410139083 13308023722868100615208625)
                  ·
                    refine ⟨9981017792151075461406469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13308023722868100615208625 9981017792151075461406469)
                    ·
                      refine ⟨1871440836028326649013713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9981017792151075461406469 1871440836028326649013713)
                      ·
                        rfl

theorem cell23_3644618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_3644618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644618 prefixEnd_3644618 := by exact prefixLift 3644618
  have htrace : WordTrace (prefixWord ++ tailWord_3644618) baseStart_3644618 baseEnd_3644618 := by
    simpa [prefixWord, tailWord_3644618, baseEnd_3644618] using wordTrace_append hprefix tailTrace_3644618
  have hstable : (prefixWord ++ tailWord_3644618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644618).length < 2 ^ (prefixWord ++ tailWord_3644618).sum := by decide
  have hdescent : baseEnd_3644618 < baseStart_3644618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644628 : List Nat := [2, 4, 1, 4, 1, 1, 1, 9]
def baseStart_3644628 : Nat := 118140960795 + 3644628 * 2 ^ 59
def prefixEnd_3644628 : Nat := 4983230072969 + 3 ^ 40 * 3644628 * 2
def baseEnd_3644628 : Nat := 69312813734624874440321

theorem tailTrace_3644628 : CollatzResearch.WordTrace tailWord_3644628 prefixEnd_3644628 69312813734624874440321 := by
  unfold tailWord_3644628
  simp only [CollatzResearch.WordTrace]
  refine ⟨66465251920071341875751269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88620335893428455834335025 66465251920071341875751269)
  ·
    refine ⟨12462234735013376601703363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66465251920071341875751269 12462234735013376601703363)
    ·
      refine ⟨18693352102520064902555045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12462234735013376601703363 18693352102520064902555045)
      ·
        refine ⟨3505003519222512169229071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18693352102520064902555045 3505003519222512169229071)
        ·
          refine ⟨5257505278833768253843607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3505003519222512169229071 5257505278833768253843607)
          ·
            refine ⟨7886257918250652380765411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5257505278833768253843607 7886257918250652380765411)
            ·
              refine ⟨11829386877375978571148117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7886257918250652380765411 11829386877375978571148117)
              ·
                refine ⟨69312813734624874440321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11829386877375978571148117 69312813734624874440321)
                ·
                  rfl

theorem cell23_3644628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 9].length) (baseStart_3644628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644628 prefixEnd_3644628 := by exact prefixLift 3644628
  have htrace : WordTrace (prefixWord ++ tailWord_3644628) baseStart_3644628 baseEnd_3644628 := by
    simpa [prefixWord, tailWord_3644628, baseEnd_3644628] using wordTrace_append hprefix tailTrace_3644628
  have hstable : (prefixWord ++ tailWord_3644628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644628).length < 2 ^ (prefixWord ++ tailWord_3644628).sum := by decide
  have hdescent : baseEnd_3644628 < baseStart_3644628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644712 : List Nat := [2, 1, 5, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_3644712 : Nat := 118140960795 + 3644712 * 2 ^ 59
def prefixEnd_3644712 : Nat := 4983230072969 + 3 ^ 40 * 3644712 * 2
def baseEnd_3644712 : Nat := 1871489103209849281238281

theorem tailTrace_3644712 : CollatzResearch.WordTrace tailWord_3644712 prefixEnd_3644712 1871489103209849281238281 := by
  unfold tailWord_3644712
  simp only [CollatzResearch.WordTrace]
  refine ⟨66466783785919183048780195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88622378381225577398373593 66466783785919183048780195)
  ·
    refine ⟨99700175678878774573170293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66466783785919183048780195 99700175678878774573170293)
    ·
      refine ⟨9346891469894885116234715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99700175678878774573170293 9346891469894885116234715)
      ·
        refine ⟨14020337204842327674352073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9346891469894885116234715 14020337204842327674352073)
        ·
          refine ⟨10515252903631745755764055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14020337204842327674352073 10515252903631745755764055)
          ·
            refine ⟨15772879355447618633646083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10515252903631745755764055 15772879355447618633646083)
            ·
              refine ⟨23659319033171427950469125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15772879355447618633646083 23659319033171427950469125)
              ·
                refine ⟨4436122318719642740712961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23659319033171427950469125 4436122318719642740712961)
                ·
                  refine ⟨3327091739039732055534721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4436122318719642740712961 3327091739039732055534721)
                  ·
                    refine ⟨2495318804279799041651041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3327091739039732055534721 2495318804279799041651041)
                    ·
                      refine ⟨1871489103209849281238281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2495318804279799041651041 1871489103209849281238281)
                      ·
                        rfl

theorem cell23_3644712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_3644712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644712 prefixEnd_3644712 := by exact prefixLift 3644712
  have htrace : WordTrace (prefixWord ++ tailWord_3644712) baseStart_3644712 baseEnd_3644712 := by
    simpa [prefixWord, tailWord_3644712, baseEnd_3644712] using wordTrace_append hprefix tailTrace_3644712
  have hstable : (prefixWord ++ tailWord_3644712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644712).length < 2 ^ (prefixWord ++ tailWord_3644712).sum := by decide
  have hdescent : baseEnd_3644712 < baseStart_3644712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644748 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 2, 5]
def baseStart_3644748 : Nat := 118140960795 + 3644748 * 2 ^ 59
def prefixEnd_3644748 : Nat := 4983230072969 + 3 ^ 40 * 3644748 * 2
def baseEnd_3644748 : Nat := 623835862837803713462705

theorem tailTrace_3644748 : CollatzResearch.WordTrace tailWord_3644748 prefixEnd_3644748 623835862837803713462705 := by
  unfold tailWord_3644748
  simp only [CollatzResearch.WordTrace]
  refine ⟨66467440299853972122935449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88623253733138629497247265 66467440299853972122935449)
  ·
    refine ⟨49850580224890479092201587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66467440299853972122935449 49850580224890479092201587)
    ·
      refine ⟨74775870337335718638302381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49850580224890479092201587 74775870337335718638302381)
      ·
        refine ⟨28040951376500894489363393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74775870337335718638302381 28040951376500894489363393)
        ·
          refine ⟨21030713532375670867022545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28040951376500894489363393 21030713532375670867022545)
          ·
            refine ⟨15773035149281753150266909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21030713532375670867022545 15773035149281753150266909)
            ·
              refine ⟨5914888180980657431350091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15773035149281753150266909 5914888180980657431350091)
              ·
                refine ⟨8872332271470986147025137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5914888180980657431350091 8872332271470986147025137)
                ·
                  refine ⟨6654249203603239610268853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8872332271470986147025137 6654249203603239610268853)
                  ·
                    refine ⟨623835862837803713462705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6654249203603239610268853 623835862837803713462705)
                    ·
                      rfl

theorem cell23_3644748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_3644748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644748 prefixEnd_3644748 := by exact prefixLift 3644748
  have htrace : WordTrace (prefixWord ++ tailWord_3644748) baseStart_3644748 baseEnd_3644748 := by
    simpa [prefixWord, tailWord_3644748, baseEnd_3644748] using wordTrace_append hprefix tailTrace_3644748
  have hstable : (prefixWord ++ tailWord_3644748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644748).length < 2 ^ (prefixWord ++ tailWord_3644748).sum := by decide
  have hdescent : baseEnd_3644748 < baseStart_3644748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644829 : List Nat := [1, 4, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_3644829 : Nat := 118140960795 + 3644829 * 2 ^ 59
def prefixEnd_3644829 : Nat := 4983230072969 + 3 ^ 40 * 3644829 * 2
def baseEnd_3644829 : Nat := 623849726815475107825081

theorem tailTrace_3644829 : CollatzResearch.WordTrace tailWord_3644829 prefixEnd_3644829 623849726815475107825081 := by
  unfold tailWord_3644829
  simp only [CollatzResearch.WordTrace]
  refine ⟨132937834912414495079569541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88625223274942996719713027 132937834912414495079569541)
  ·
    refine ⟨24925844046077717827419289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132937834912414495079569541 24925844046077717827419289)
    ·
      refine ⟨18694383034558288370564467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24925844046077717827419289 18694383034558288370564467)
      ·
        refine ⟨28041574551837432555846701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18694383034558288370564467 28041574551837432555846701)
        ·
          refine ⟨10515590456939037208442513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28041574551837432555846701 10515590456939037208442513)
          ·
            refine ⟨7886692842704277906331885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10515590456939037208442513 7886692842704277906331885)
            ·
              refine ⟨2957509816014104214874457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7886692842704277906331885 2957509816014104214874457)
              ·
                refine ⟨2218132362010578161155843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957509816014104214874457 2218132362010578161155843)
                ·
                  refine ⟨3327198543015867241733765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218132362010578161155843 3327198543015867241733765)
                  ·
                    refine ⟨623849726815475107825081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3327198543015867241733765 623849726815475107825081)
                    ·
                      rfl

theorem cell23_3644829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_3644829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644829 prefixEnd_3644829 := by exact prefixLift 3644829
  have htrace : WordTrace (prefixWord ++ tailWord_3644829) baseStart_3644829 baseEnd_3644829 := by
    simpa [prefixWord, tailWord_3644829, baseEnd_3644829] using wordTrace_append hprefix tailTrace_3644829
  have hstable : (prefixWord ++ tailWord_3644829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644829).length < 2 ^ (prefixWord ++ tailWord_3644829).sum := by decide
  have hdescent : baseEnd_3644829 < baseStart_3644829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644841 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 1, 7, 4]
def baseStart_3644841 : Nat := 118140960795 + 3644841 * 2 ^ 59
def prefixEnd_3644841 : Nat := 4983230072969 + 3 ^ 40 * 3644841 * 2
def baseEnd_3644841 : Nat := 1871555342214279276525187

theorem tailTrace_3644841 : CollatzResearch.WordTrace tailWord_3644841 prefixEnd_3644841 1871555342214279276525187 := by
  unfold tailWord_3644841
  simp only [CollatzResearch.WordTrace]
  refine ⟨132938272588371021129006377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88625515058914014086004251 132938272588371021129006377)
  ·
    refine ⟨99703704441278265846754783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132938272588371021129006377 99703704441278265846754783)
    ·
      refine ⟨149555556661917398770132175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99703704441278265846754783 149555556661917398770132175)
      ·
        refine ⟨224333334992876098155198263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149555556661917398770132175 224333334992876098155198263)
        ·
          refine ⟨336500002489314147232797395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224333334992876098155198263 336500002489314147232797395)
          ·
            refine ⟨504750003733971220849196093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336500002489314147232797395 504750003733971220849196093)
            ·
              refine ⟨189281251400239207818448535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 504750003733971220849196093 189281251400239207818448535)
              ·
                refine ⟨283921877100358811727672803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189281251400239207818448535 283921877100358811727672803)
                ·
                  refine ⟨425882815650538217591509205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283921877100358811727672803 425882815650538217591509205)
                  ·
                    refine ⟨9981628491809489474800997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 425882815650538217591509205 9981628491809489474800997)
                    ·
                      refine ⟨1871555342214279276525187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9981628491809489474800997 1871555342214279276525187)
                      ·
                        rfl

theorem cell23_3644841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_3644841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644841 prefixEnd_3644841 := by exact prefixLift 3644841
  have htrace : WordTrace (prefixWord ++ tailWord_3644841) baseStart_3644841 baseEnd_3644841 := by
    simpa [prefixWord, tailWord_3644841, baseEnd_3644841] using wordTrace_append hprefix tailTrace_3644841
  have hstable : (prefixWord ++ tailWord_3644841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644841).length < 2 ^ (prefixWord ++ tailWord_3644841).sum := by decide
  have hdescent : baseEnd_3644841 < baseStart_3644841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644851 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 5, 6]
def baseStart_3644851 : Nat := 118140960795 + 3644851 * 2 ^ 59
def prefixEnd_3644851 : Nat := 4983230072969 + 3 ^ 40 * 3644851 * 2
def baseEnd_3644851 : Nat := 623853492340274745800047

theorem tailTrace_3644851 : CollatzResearch.WordTrace tailWord_3644851 prefixEnd_3644851 623853492340274745800047 := by
  unfold tailWord_3644851
  simp only [CollatzResearch.WordTrace]
  refine ⟨132938637318334792836870407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88625758212223195224580271 132938637318334792836870407)
  ·
    refine ⟨199407955977502189255305611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132938637318334792836870407 199407955977502189255305611)
    ·
      refine ⟨299111933966253283882958417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199407955977502189255305611 299111933966253283882958417)
      ·
        refine ⟨224333950474689962912218813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299111933966253283882958417 224333950474689962912218813)
        ·
          refine ⟨84125231428008736092082055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224333950474689962912218813 84125231428008736092082055)
          ·
            refine ⟨126187847142013104138123083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84125231428008736092082055 126187847142013104138123083)
            ·
              refine ⟨189281770713019656207184625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126187847142013104138123083 189281770713019656207184625)
              ·
                refine ⟨141961328034764742155388469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189281770713019656207184625 141961328034764742155388469)
                ·
                  refine ⟨13308874503259194577067669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141961328034764742155388469 13308874503259194577067669)
                  ·
                    refine ⟨623853492340274745800047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13308874503259194577067669 623853492340274745800047)
                    ·
                      rfl

theorem cell23_3644851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 6].length) (baseStart_3644851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644851 prefixEnd_3644851 := by exact prefixLift 3644851
  have htrace : WordTrace (prefixWord ++ tailWord_3644851) baseStart_3644851 baseEnd_3644851 := by
    simpa [prefixWord, tailWord_3644851, baseEnd_3644851] using wordTrace_append hprefix tailTrace_3644851
  have hstable : (prefixWord ++ tailWord_3644851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644851).length < 2 ^ (prefixWord ++ tailWord_3644851).sum := by decide
  have hdescent : baseEnd_3644851 < baseStart_3644851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644886 : List Nat := [5, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_3644886 : Nat := 118140960795 + 3644886 * 2 ^ 59
def prefixEnd_3644886 : Nat := 4983230072969 + 3 ^ 40 * 3644886 * 2
def baseEnd_3644886 : Nat := 1871578448843731600462481

theorem tailTrace_3644886 : CollatzResearch.WordTrace tailWord_3644886 prefixEnd_3644886 1871578448843731600462481 := by
  unfold tailWord_3644886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8308744617075499613399657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88626609248805329209596341 8308744617075499613399657)
  ·
    refine ⟨6231558462806624710049743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8308744617075499613399657 6231558462806624710049743)
    ·
      refine ⟨9347337694209937065074615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6231558462806624710049743 9347337694209937065074615)
      ·
        refine ⟨14021006541314905597611923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9347337694209937065074615 14021006541314905597611923)
        ·
          refine ⟨21031509811972358396417885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14021006541314905597611923 21031509811972358396417885)
          ·
            refine ⟨7886816179489634398656707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21031509811972358396417885 7886816179489634398656707)
            ·
              refine ⟨11830224269234451597985061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7886816179489634398656707 11830224269234451597985061)
              ·
                refine ⟨2218167050481459674622199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11830224269234451597985061 2218167050481459674622199)
                ·
                  refine ⟨3327250575722189511933299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218167050481459674622199 3327250575722189511933299)
                  ·
                    refine ⟨4990875863583284267899949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3327250575722189511933299 4990875863583284267899949)
                    ·
                      refine ⟨1871578448843731600462481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4990875863583284267899949 1871578448843731600462481)
                      ·
                        rfl

theorem cell23_3644886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_3644886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644886 prefixEnd_3644886 := by exact prefixLift 3644886
  have htrace : WordTrace (prefixWord ++ tailWord_3644886) baseStart_3644886 baseEnd_3644886 := by
    simpa [prefixWord, tailWord_3644886, baseEnd_3644886] using wordTrace_append hprefix tailTrace_3644886
  have hstable : (prefixWord ++ tailWord_3644886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644886).length < 2 ^ (prefixWord ++ tailWord_3644886).sum := by decide
  have hdescent : baseEnd_3644886 < baseStart_3644886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644925 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_3644925 : Nat := 118140960795 + 3644925 * 2 ^ 59
def prefixEnd_3644925 : Nat := 4983230072969 + 3 ^ 40 * 3644925 * 2
def baseEnd_3644925 : Nat := 1871598474589256947874801

theorem tailTrace_3644925 : CollatzResearch.WordTrace tailWord_3644925 prefixEnd_3644925 1871598474589256947874801 := by
  unfold tailWord_3644925
  simp only [CollatzResearch.WordTrace]
  refine ⟨132941336320066703475064229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88627557546711135650042819 132941336320066703475064229)
  ·
    refine ⟨24926500560012506901574543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132941336320066703475064229 24926500560012506901574543)
    ·
      refine ⟨37389750840018760352361815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24926500560012506901574543 37389750840018760352361815)
      ·
        refine ⟨56084626260028140528542723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37389750840018760352361815 56084626260028140528542723)
        ·
          refine ⟨84126939390042210792814085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56084626260028140528542723 84126939390042210792814085)
          ·
            refine ⟨15773801135632914523652641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84126939390042210792814085 15773801135632914523652641)
            ·
              refine ⟨11830350851724685892739481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15773801135632914523652641 11830350851724685892739481)
              ·
                refine ⟨8872763138793514419554611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11830350851724685892739481 8872763138793514419554611)
                ·
                  refine ⟨13309144708190271629331917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8872763138793514419554611 13309144708190271629331917)
                  ·
                    refine ⟨4990929265571351860999469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13309144708190271629331917 4990929265571351860999469)
                    ·
                      refine ⟨1871598474589256947874801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4990929265571351860999469 1871598474589256947874801)
                      ·
                        rfl

theorem cell23_3644925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_3644925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644925 prefixEnd_3644925 := by exact prefixLift 3644925
  have htrace : WordTrace (prefixWord ++ tailWord_3644925) baseStart_3644925 baseEnd_3644925 := by
    simpa [prefixWord, tailWord_3644925, baseEnd_3644925] using wordTrace_append hprefix tailTrace_3644925
  have hstable : (prefixWord ++ tailWord_3644925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644925).length < 2 ^ (prefixWord ++ tailWord_3644925).sum := by decide
  have hdescent : baseEnd_3644925 < baseStart_3644925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3644985 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3644985 : Nat := 118140960795 + 3644985 * 2 ^ 59
def prefixEnd_3644985 : Nat := 4983230072969 + 3 ^ 40 * 3644985 * 2
def baseEnd_3644985 : Nat := 1871629283428526713124525

theorem tailTrace_3644985 : CollatzResearch.WordTrace tailWord_3644985 prefixEnd_3644985 1871629283428526713124525 := by
  unfold tailWord_3644985
  simp only [CollatzResearch.WordTrace]
  refine ⟨132943524699849333722248409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88629016466566222481498939 132943524699849333722248409)
  ·
    refine ⟨99707643524887000291686307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132943524699849333722248409 99707643524887000291686307)
    ·
      refine ⟨149561465287330500437529461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99707643524887000291686307 149561465287330500437529461)
      ·
        refine ⟨14021387370687234416018387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149561465287330500437529461 14021387370687234416018387)
        ·
          refine ⟨21032081056030851624027581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14021387370687234416018387 21032081056030851624027581)
          ·
            refine ⟨7887030396011569359010343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21032081056030851624027581 7887030396011569359010343)
            ·
              refine ⟨11830545594017354038515515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7887030396011569359010343 11830545594017354038515515)
              ·
                refine ⟨17745818391026031057773273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11830545594017354038515515 17745818391026031057773273)
                ·
                  refine ⟨13309363793269523293329955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17745818391026031057773273 13309363793269523293329955)
                  ·
                    refine ⟨19964045689904284939994933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13309363793269523293329955 19964045689904284939994933)
                    ·
                      refine ⟨1871629283428526713124525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19964045689904284939994933 1871629283428526713124525)
                      ·
                        rfl

theorem cell23_3644985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3644985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3644985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3644985 prefixEnd_3644985 := by exact prefixLift 3644985
  have htrace : WordTrace (prefixWord ++ tailWord_3644985) baseStart_3644985 baseEnd_3644985 := by
    simpa [prefixWord, tailWord_3644985, baseEnd_3644985] using wordTrace_append hprefix tailTrace_3644985
  have hstable : (prefixWord ++ tailWord_3644985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3644985).length < 2 ^ (prefixWord ++ tailWord_3644985).sum := by decide
  have hdescent : baseEnd_3644985 < baseStart_3644985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3644985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645018 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 3, 7]
def baseStart_3645018 : Nat := 118140960795 + 3645018 * 2 ^ 59
def prefixEnd_3645018 : Nat := 4983230072969 + 3 ^ 40 * 3645018 * 2
def baseEnd_3645018 : Nat := 623882076096708361337291

theorem tailTrace_3645018 : CollatzResearch.WordTrace tailWord_3645018 prefixEnd_3645018 623882076096708361337291 := by
  unfold tailWord_3645018
  simp only [CollatzResearch.WordTrace]
  refine ⟨33236182077182445089549927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88629818872486520238799805 33236182077182445089549927)
  ·
    refine ⟨49854273115773667634324891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33236182077182445089549927 49854273115773667634324891)
    ·
      refine ⟨74781409673660501451487337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49854273115773667634324891 74781409673660501451487337)
      ·
        refine ⟨56086057255245376088615503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74781409673660501451487337 56086057255245376088615503)
        ·
          refine ⟨84129085882868064132923255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56086057255245376088615503 84129085882868064132923255)
          ·
            refine ⟨126193628824302096199384883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84129085882868064132923255 126193628824302096199384883)
            ·
              refine ⟨189290443236453144299077325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126193628824302096199384883 189290443236453144299077325)
              ·
                refine ⟨70983916213669929112153997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189290443236453144299077325 70983916213669929112153997)
                ·
                  refine ⟨26618968580126223417057749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70983916213669929112153997 26618968580126223417057749)
                  ·
                    refine ⟨623882076096708361337291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26618968580126223417057749 623882076096708361337291)
                    ·
                      rfl

theorem cell23_3645018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_3645018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645018 prefixEnd_3645018 := by exact prefixLift 3645018
  have htrace : WordTrace (prefixWord ++ tailWord_3645018) baseStart_3645018 baseEnd_3645018 := by
    simpa [prefixWord, tailWord_3645018, baseEnd_3645018] using wordTrace_append hprefix tailTrace_3645018
  have hstable : (prefixWord ++ tailWord_3645018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645018).length < 2 ^ (prefixWord ++ tailWord_3645018).sum := by decide
  have hdescent : baseEnd_3645018 < baseStart_3645018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645089 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3645089 : Nat := 118140960795 + 3645089 * 2 ^ 59
def prefixEnd_3645089 : Nat := 4983230072969 + 3 ^ 40 * 3645089 * 2
def baseEnd_3645089 : Nat := 1871682685416594306224047

theorem tailTrace_3645089 : CollatzResearch.WordTrace tailWord_3645089 prefixEnd_3645089 1871682685416594306224047 := by
  unfold tailWord_3645089
  simp only [CollatzResearch.WordTrace]
  refine ⟨132947317891472559484034321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88631545260981706322689547 132947317891472559484034321)
  ·
    refine ⟨99710488418604419613025741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132947317891472559484034321 99710488418604419613025741)
    ·
      refine ⟨37391433156976657354884653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99710488418604419613025741 37391433156976657354884653)
      ·
        refine ⟨14021787433866246508081745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37391433156976657354884653 14021787433866246508081745)
        ·
          refine ⟨10516340575399684881061309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14021787433866246508081745 10516340575399684881061309)
          ·
            refine ⟨3943627715774881830397991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10516340575399684881061309 3943627715774881830397991)
            ·
              refine ⟨5915441573662322745596987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3943627715774881830397991 5915441573662322745596987)
              ·
                refine ⟨8873162360493484118395481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5915441573662322745596987 8873162360493484118395481)
                ·
                  refine ⟨6654871770370113088796611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8873162360493484118395481 6654871770370113088796611)
                  ·
                    refine ⟨9982307655555169633194917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6654871770370113088796611 9982307655555169633194917)
                    ·
                      refine ⟨1871682685416594306224047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9982307655555169633194917 1871682685416594306224047)
                      ·
                        rfl

theorem cell23_3645089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3645089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645089 prefixEnd_3645089 := by exact prefixLift 3645089
  have htrace : WordTrace (prefixWord ++ tailWord_3645089) baseStart_3645089 baseEnd_3645089 := by
    simpa [prefixWord, tailWord_3645089, baseEnd_3645089] using wordTrace_append hprefix tailTrace_3645089
  have hstable : (prefixWord ++ tailWord_3645089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645089).length < 2 ^ (prefixWord ++ tailWord_3645089).sum := by decide
  have hdescent : baseEnd_3645089 < baseStart_3645089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645092 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_3645092 : Nat := 118140960795 + 3645092 * 2 ^ 59
def prefixEnd_3645092 : Nat := 4983230072969 + 3 ^ 40 * 3645092 * 2
def baseEnd_3645092 : Nat := 1871684225858557794486533

theorem tailTrace_3645092 : CollatzResearch.WordTrace tailWord_3645092 prefixEnd_3645092 1871684225858557794486533 := by
  unfold tailWord_3645092
  simp only [CollatzResearch.WordTrace]
  refine ⟨66473713655230845498196765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88631618206974460664262353 66473713655230845498196765)
  ·
    refine ⟨24927642620711567061823787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66473713655230845498196765 24927642620711567061823787)
    ·
      refine ⟨37391463931067350592735681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24927642620711567061823787 37391463931067350592735681)
      ·
        refine ⟨28043597948300512944551761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37391463931067350592735681 28043597948300512944551761)
        ·
          refine ⟨21032698461225384708413821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28043597948300512944551761 21032698461225384708413821)
          ·
            refine ⟨7887261922959519265655183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21032698461225384708413821 7887261922959519265655183)
            ·
              refine ⟨11830892884439278898482775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7887261922959519265655183 11830892884439278898482775)
              ·
                refine ⟨17746339326658918347724163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11830892884439278898482775 17746339326658918347724163)
                ·
                  refine ⟨26619508989988377521586245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17746339326658918347724163 26619508989988377521586245)
                  ·
                    refine ⟨4991157935622820785297421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26619508989988377521586245 4991157935622820785297421)
                    ·
                      refine ⟨1871684225858557794486533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4991157935622820785297421 1871684225858557794486533)
                      ·
                        rfl

theorem cell23_3645092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_3645092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645092 prefixEnd_3645092 := by exact prefixLift 3645092
  have htrace : WordTrace (prefixWord ++ tailWord_3645092) baseStart_3645092 baseEnd_3645092 := by
    simpa [prefixWord, tailWord_3645092, baseEnd_3645092] using wordTrace_append hprefix tailTrace_3645092
  have hstable : (prefixWord ++ tailWord_3645092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645092).length < 2 ^ (prefixWord ++ tailWord_3645092).sum := by decide
  have hdescent : baseEnd_3645092 < baseStart_3645092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645126 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_3645126 : Nat := 118140960795 + 3645126 * 2 ^ 59
def prefixEnd_3645126 : Nat := 4983230072969 + 3 ^ 40 * 3645126 * 2
def baseEnd_3645126 : Nat := 1871701684200810661461377

theorem tailTrace_3645126 : CollatzResearch.WordTrace tailWord_3645126 prefixEnd_3645126 1871701684200810661461377 := by
  unfold tailWord_3645126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4154645856010578587597851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88632444928225676535420821 4154645856010578587597851)
  ·
    refine ⟨6231968784015867881396777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4154645856010578587597851 6231968784015867881396777)
    ·
      refine ⟨4673976588011900911047583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6231968784015867881396777 4673976588011900911047583)
      ·
        refine ⟨7010964882017851366571375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4673976588011900911047583 7010964882017851366571375)
        ·
          refine ⟨10516447323026777049857063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7010964882017851366571375 10516447323026777049857063)
          ·
            refine ⟨15774670984540165574785595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10516447323026777049857063 15774670984540165574785595)
            ·
              refine ⟨23662006476810248362178393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15774670984540165574785595 23662006476810248362178393)
              ·
                refine ⟨17746504857607686271633795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23662006476810248362178393 17746504857607686271633795)
                ·
                  refine ⟨26619757286411529407450693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17746504857607686271633795 26619757286411529407450693)
                  ·
                    refine ⟨4991204491202161763897005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26619757286411529407450693 4991204491202161763897005)
                    ·
                      refine ⟨1871701684200810661461377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4991204491202161763897005 1871701684200810661461377)
                      ·
                        rfl

theorem cell23_3645126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_3645126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645126 prefixEnd_3645126 := by exact prefixLift 3645126
  have htrace : WordTrace (prefixWord ++ tailWord_3645126) baseStart_3645126 baseEnd_3645126 := by
    simpa [prefixWord, tailWord_3645126, baseEnd_3645126] using wordTrace_append hprefix tailTrace_3645126
  have hstable : (prefixWord ++ tailWord_3645126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645126).length < 2 ^ (prefixWord ++ tailWord_3645126).sum := by decide
  have hdescent : baseEnd_3645126 < baseStart_3645126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645175 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_3645175 : Nat := 118140960795 + 3645175 * 2 ^ 59
def prefixEnd_3645175 : Nat := 4983230072969 + 3 ^ 40 * 3645175 * 2
def baseEnd_3645175 : Nat := 1871726844752880969748651

theorem tailTrace_3645175 : CollatzResearch.WordTrace tailWord_3645175 prefixEnd_3645175 1871726844752880969748651 := by
  unfold tailWord_3645175
  simp only [CollatzResearch.WordTrace]
  refine ⟨132950454569160996171664979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88633636379440664114443319 132950454569160996171664979)
  ·
    refine ⟨199425681853741494257497469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132950454569160996171664979 199425681853741494257497469)
    ·
      refine ⟨74784630695153060346561551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199425681853741494257497469 74784630695153060346561551)
      ·
        refine ⟨112176946042729590519842327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74784630695153060346561551 112176946042729590519842327)
        ·
          refine ⟨168265419064094385779763491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112176946042729590519842327 168265419064094385779763491)
          ·
            refine ⟨252398128596141578669645237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168265419064094385779763491 252398128596141578669645237)
            ·
              refine ⟨23662324555888273000279241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252398128596141578669645237 23662324555888273000279241)
              ·
                refine ⟨17746743416916204750209431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23662324555888273000279241 17746743416916204750209431)
                ·
                  refine ⟨26620115125374307125314147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17746743416916204750209431 26620115125374307125314147)
                  ·
                    refine ⟨39930172688061460687971221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26620115125374307125314147 39930172688061460687971221)
                    ·
                      refine ⟨1871726844752880969748651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39930172688061460687971221 1871726844752880969748651)
                      ·
                        rfl

theorem cell23_3645175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_3645175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645175 prefixEnd_3645175 := by exact prefixLift 3645175
  have htrace : WordTrace (prefixWord ++ tailWord_3645175) baseStart_3645175 baseEnd_3645175 := by
    simpa [prefixWord, tailWord_3645175, baseEnd_3645175] using wordTrace_append hprefix tailTrace_3645175
  have hstable : (prefixWord ++ tailWord_3645175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645175).length < 2 ^ (prefixWord ++ tailWord_3645175).sum := by decide
  have hdescent : baseEnd_3645175 < baseStart_3645175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645179 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 3, 2, 2]
def baseStart_3645179 : Nat := 118140960795 + 3645179 * 2 ^ 59
def prefixEnd_3645179 : Nat := 4983230072969 + 3 ^ 40 * 3645179 * 2
def baseEnd_3645179 : Nat := 1871728898675498954098633

theorem tailTrace_3645179 : CollatzResearch.WordTrace tailWord_3645179 prefixEnd_3645179 1871728898675498954098633 := by
  unfold tailWord_3645179
  simp only [CollatzResearch.WordTrace]
  refine ⟨132950600461146504854810591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88633733640764336569873727 132950600461146504854810591)
  ·
    refine ⟨199425900691719757282215887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132950600461146504854810591 199425900691719757282215887)
    ·
      refine ⟨299138851037579635923323831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199425900691719757282215887 299138851037579635923323831)
      ·
        refine ⟨448708276556369453884985747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299138851037579635923323831 448708276556369453884985747)
        ·
          refine ⟨673062414834554180827478621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448708276556369453884985747 673062414834554180827478621)
          ·
            refine ⟨252398405562957817810304483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 673062414834554180827478621 252398405562957817810304483)
            ·
              refine ⟨378597608344436726715456725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252398405562957817810304483 378597608344436726715456725)
              ·
                refine ⟨8873381445572735782393517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 378597608344436726715456725 8873381445572735782393517)
                ·
                  refine ⟨3327518042089775918397569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8873381445572735782393517 3327518042089775918397569)
                  ·
                    refine ⟨2495638531567331938798177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3327518042089775918397569 2495638531567331938798177)
                    ·
                      refine ⟨1871728898675498954098633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2495638531567331938798177 1871728898675498954098633)
                      ·
                        rfl

theorem cell23_3645179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 3, 2, 2].length) (baseStart_3645179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645179 prefixEnd_3645179 := by exact prefixLift 3645179
  have htrace : WordTrace (prefixWord ++ tailWord_3645179) baseStart_3645179 baseEnd_3645179 := by
    simpa [prefixWord, tailWord_3645179, baseEnd_3645179] using wordTrace_append hprefix tailTrace_3645179
  have hstable : (prefixWord ++ tailWord_3645179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645179).length < 2 ^ (prefixWord ++ tailWord_3645179).sum := by decide
  have hdescent : baseEnd_3645179 < baseStart_3645179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645185 : List Nat := [1, 2, 4, 1, 1, 1, 3, 10]
def baseStart_3645185 : Nat := 118140960795 + 3645185 * 2 ^ 59
def prefixEnd_3645185 : Nat := 4983230072969 + 3 ^ 40 * 3645185 * 2
def baseEnd_3645185 : Nat := 69323406650349108541615

theorem tailTrace_3645185 : CollatzResearch.WordTrace tailWord_3645185 prefixEnd_3645185 69323406650349108541615 := by
  unfold tailWord_3645185
  simp only [CollatzResearch.WordTrace]
  refine ⟨132950819299124767879529009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88633879532749845253019339 132950819299124767879529009)
  ·
    refine ⟨99713114474343575909646757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132950819299124767879529009 99713114474343575909646757)
    ·
      refine ⟨18696208963939420483058767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99713114474343575909646757 18696208963939420483058767)
      ·
        refine ⟨28044313445909130724588151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18696208963939420483058767 28044313445909130724588151)
        ·
          refine ⟨42066470168863696086882227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28044313445909130724588151 42066470168863696086882227)
          ·
            refine ⟨63099705253295544130323341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42066470168863696086882227 63099705253295544130323341)
            ·
              refine ⟨23662389469985829048871253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63099705253295544130323341 23662389469985829048871253)
              ·
                refine ⟨69323406650349108541615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23662389469985829048871253 69323406650349108541615)
                ·
                  rfl

theorem cell23_3645185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 10].length) (baseStart_3645185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645185 prefixEnd_3645185 := by exact prefixLift 3645185
  have htrace : WordTrace (prefixWord ++ tailWord_3645185) baseStart_3645185 baseEnd_3645185 := by
    simpa [prefixWord, tailWord_3645185, baseEnd_3645185] using wordTrace_append hprefix tailTrace_3645185
  have hstable : (prefixWord ++ tailWord_3645185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645185).length < 2 ^ (prefixWord ++ tailWord_3645185).sum := by decide
  have hdescent : baseEnd_3645185 < baseStart_3645185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645192 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_3645192 : Nat := 118140960795 + 3645192 * 2 ^ 59
def prefixEnd_3645192 : Nat := 4983230072969 + 3 ^ 40 * 3645192 * 2
def baseEnd_3645192 : Nat := 1871735573924007403236073

theorem tailTrace_3645192 : CollatzResearch.WordTrace tailWord_3645192 prefixEnd_3645192 1871735573924007403236073 := by
  unfold tailWord_3645192
  simp only [CollatzResearch.WordTrace]
  refine ⟨66475537305049704037516915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88634049740066272050022553 66475537305049704037516915)
  ·
    refine ⟨99713305957574556056275373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66475537305049704037516915 99713305957574556056275373)
    ·
      refine ⟨37392489734090458521103265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99713305957574556056275373 37392489734090458521103265)
      ·
        refine ⟨28044367300567843890827449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37392489734090458521103265 28044367300567843890827449)
        ·
          refine ⟨21033275475425882918120587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28044367300567843890827449 21033275475425882918120587)
          ·
            refine ⟨31549913213138824377180881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21033275475425882918120587 31549913213138824377180881)
            ·
              refine ⟨23662434909854118282885661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31549913213138824377180881 23662434909854118282885661)
              ·
                refine ⟨8873413091195294356082123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23662434909854118282885661 8873413091195294356082123)
                ·
                  refine ⟨13310119636792941534123185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8873413091195294356082123 13310119636792941534123185)
                  ·
                    refine ⟨9982589727594706150592389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13310119636792941534123185 9982589727594706150592389)
                    ·
                      refine ⟨1871735573924007403236073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9982589727594706150592389 1871735573924007403236073)
                      ·
                        rfl

theorem cell23_3645192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_3645192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645192 prefixEnd_3645192 := by exact prefixLift 3645192
  have htrace : WordTrace (prefixWord ++ tailWord_3645192) baseStart_3645192 baseEnd_3645192 := by
    simpa [prefixWord, tailWord_3645192, baseEnd_3645192] using wordTrace_append hprefix tailTrace_3645192
  have hstable : (prefixWord ++ tailWord_3645192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645192).length < 2 ^ (prefixWord ++ tailWord_3645192).sum := by decide
  have hdescent : baseEnd_3645192 < baseStart_3645192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645216 : List Nat := [2, 1, 1, 5, 1, 1, 5, 1, 1, 2, 3]
def baseStart_3645216 : Nat := 118140960795 + 3645216 * 2 ^ 59
def prefixEnd_3645216 : Nat := 4983230072969 + 3 ^ 40 * 3645216 * 2
def baseEnd_3645216 : Nat := 1871747897459715309335963

theorem tailTrace_3645216 : CollatzResearch.WordTrace tailWord_3645216 prefixEnd_3645216 1871747897459715309335963 := by
  unfold tailWord_3645216
  simp only [CollatzResearch.WordTrace]
  refine ⟨66475974981006230086953751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88634633308008306782605001 66475974981006230086953751)
  ·
    refine ⟨99713962471509345130430627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66475974981006230086953751 99713962471509345130430627)
    ·
      refine ⟨149570943707264017695645941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99713962471509345130430627 149570943707264017695645941)
      ·
        refine ⟨14022275972556001658966807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149570943707264017695645941 14022275972556001658966807)
        ·
          refine ⟨21033413958834002488450211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14022275972556001658966807 21033413958834002488450211)
          ·
            refine ⟨31550120938251003732675317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21033413958834002488450211 31550120938251003732675317)
            ·
              refine ⟨2957823837961031599938311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31550120938251003732675317 2957823837961031599938311)
              ·
                refine ⟨4436735756941547399907467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2957823837961031599938311 4436735756941547399907467)
                ·
                  refine ⟨6655103635412321099861201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4436735756941547399907467 6655103635412321099861201)
                  ·
                    refine ⟨4991327726559240824895901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6655103635412321099861201 4991327726559240824895901)
                    ·
                      refine ⟨1871747897459715309335963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4991327726559240824895901 1871747897459715309335963)
                      ·
                        rfl

theorem cell23_3645216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_3645216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645216 prefixEnd_3645216 := by exact prefixLift 3645216
  have htrace : WordTrace (prefixWord ++ tailWord_3645216) baseStart_3645216 baseEnd_3645216 := by
    simpa [prefixWord, tailWord_3645216, baseEnd_3645216] using wordTrace_append hprefix tailTrace_3645216
  have hstable : (prefixWord ++ tailWord_3645216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645216).length < 2 ^ (prefixWord ++ tailWord_3645216).sum := by decide
  have hdescent : baseEnd_3645216 < baseStart_3645216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645246 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_3645246 : Nat := 118140960795 + 3645246 * 2 ^ 59
def prefixEnd_3645246 : Nat := 4983230072969 + 3 ^ 40 * 3645246 * 2
def baseEnd_3645246 : Nat := 1871763301879350191960825

theorem tailTrace_3645246 : CollatzResearch.WordTrace tailWord_3645246 prefixEnd_3645246 1871763301879350191960825 := by
  unfold tailWord_3645246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16619130518987971912187449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88635362767935850198333061 16619130518987971912187449)
  ·
    refine ⟨12464347889240978934140587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16619130518987971912187449 12464347889240978934140587)
    ·
      refine ⟨18696521833861468401210881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12464347889240978934140587 18696521833861468401210881)
      ·
        refine ⟨14022391375396101300908161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18696521833861468401210881 14022391375396101300908161)
        ·
          refine ⟨10516793531547075975681121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14022391375396101300908161 10516793531547075975681121)
          ·
            refine ⟨7887595148660306981760841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10516793531547075975681121 7887595148660306981760841)
            ·
              refine ⟨5915696361495230236320631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7887595148660306981760841 5915696361495230236320631)
              ·
                refine ⟨8873544542242845354480947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5915696361495230236320631 8873544542242845354480947)
                ·
                  refine ⟨13310316813364268031721421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8873544542242845354480947 13310316813364268031721421)
                  ·
                    refine ⟨4991368805011600511895533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13310316813364268031721421 4991368805011600511895533)
                    ·
                      refine ⟨1871763301879350191960825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4991368805011600511895533 1871763301879350191960825)
                      ·
                        rfl

theorem cell23_3645246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_3645246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645246 prefixEnd_3645246 := by exact prefixLift 3645246
  have htrace : WordTrace (prefixWord ++ tailWord_3645246) baseStart_3645246 baseEnd_3645246 := by
    simpa [prefixWord, tailWord_3645246, baseEnd_3645246] using wordTrace_append hprefix tailTrace_3645246
  have hstable : (prefixWord ++ tailWord_3645246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645246).length < 2 ^ (prefixWord ++ tailWord_3645246).sum := by decide
  have hdescent : baseEnd_3645246 < baseStart_3645246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645292 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 7]
def baseStart_3645292 : Nat := 118140960795 + 3645292 * 2 ^ 59
def prefixEnd_3645292 : Nat := 4983230072969 + 3 ^ 40 * 3645292 * 2
def baseEnd_3645292 : Nat := 207976324665495223553957

theorem tailTrace_3645292 : CollatzResearch.WordTrace tailWord_3645292 prefixEnd_3645292 207976324665495223553957 := by
  unfold tailWord_3645292
  simp only [CollatzResearch.WordTrace]
  refine ⟨66477360954868562576837065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88636481273158083435782753 66477360954868562576837065)
  ·
    refine ⟨49858020716151421932627799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66477360954868562576837065 49858020716151421932627799)
    ·
      refine ⟨74787031074227132898941699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49858020716151421932627799 74787031074227132898941699)
      ·
        refine ⟨112180546611340699348412549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74787031074227132898941699 112180546611340699348412549)
        ·
          refine ⟨21033852489626381127827353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112180546611340699348412549 21033852489626381127827353)
          ·
            refine ⟨15775389367219785845870515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21033852489626381127827353 15775389367219785845870515)
            ·
              refine ⟨23663084050829678768805773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15775389367219785845870515 23663084050829678768805773)
              ·
                refine ⟨8873656519061129538302165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23663084050829678768805773 8873656519061129538302165)
                ·
                  refine ⟨207976324665495223553957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8873656519061129538302165 207976324665495223553957)
                  ·
                    rfl

theorem cell23_3645292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 7].length) (baseStart_3645292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645292 prefixEnd_3645292 := by exact prefixLift 3645292
  have htrace : WordTrace (prefixWord ++ tailWord_3645292) baseStart_3645292 baseEnd_3645292 := by
    simpa [prefixWord, tailWord_3645292, baseEnd_3645292] using wordTrace_append hprefix tailTrace_3645292
  have hstable : (prefixWord ++ tailWord_3645292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645292).length < 2 ^ (prefixWord ++ tailWord_3645292).sum := by decide
  have hdescent : baseEnd_3645292 < baseStart_3645292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645343 : List Nat := [1, 1, 2, 5, 3, 1, 3, 2, 5]
def baseStart_3645343 : Nat := 118140960795 + 3645343 * 2 ^ 59
def prefixEnd_3645343 : Nat := 4983230072969 + 3 ^ 40 * 3645343 * 2
def baseEnd_3645343 : Nat := 207979234389204034716431

theorem tailTrace_3645343 : CollatzResearch.WordTrace tailWord_3645343 prefixEnd_3645343 207979234389204034716431 := by
  unfold tailWord_3645343
  simp only [CollatzResearch.WordTrace]
  refine ⟨132956582032552360863780683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88637721355034907242520455 132956582032552360863780683)
  ·
    refine ⟨199434873048828541295671025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132956582032552360863780683 199434873048828541295671025)
    ·
      refine ⟨149576154786621405971753269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199434873048828541295671025 149576154786621405971753269)
      ·
        refine ⟨14022764511245756809851869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149576154786621405971753269 14022764511245756809851869)
        ·
          refine ⟨5258536691717158803694451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14022764511245756809851869 5258536691717158803694451)
          ·
            refine ⟨7887805037575738205541677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5258536691717158803694451 7887805037575738205541677)
            ·
              refine ⟨2957926889090901827078129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7887805037575738205541677 2957926889090901827078129)
              ·
                refine ⟨2218445166818176370308597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957926889090901827078129 2218445166818176370308597)
                ·
                  refine ⟨207979234389204034716431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2218445166818176370308597 207979234389204034716431)
                  ·
                    rfl

theorem cell23_3645343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 5].length) (baseStart_3645343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645343 prefixEnd_3645343 := by exact prefixLift 3645343
  have htrace : WordTrace (prefixWord ++ tailWord_3645343) baseStart_3645343 baseEnd_3645343 := by
    simpa [prefixWord, tailWord_3645343, baseEnd_3645343] using wordTrace_append hprefix tailTrace_3645343
  have hstable : (prefixWord ++ tailWord_3645343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645343).length < 2 ^ (prefixWord ++ tailWord_3645343).sum := by decide
  have hdescent : baseEnd_3645343 < baseStart_3645343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645359 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 1, 6, 2]
def baseStart_3645359 : Nat := 118140960795 + 3645359 * 2 ^ 59
def prefixEnd_3645359 : Nat := 4983230072969 + 3 ^ 40 * 3645359 * 2
def baseEnd_3645359 : Nat := 1871821325193308249847805

theorem tailTrace_3645359 : CollatzResearch.WordTrace tailWord_3645359 prefixEnd_3645359 1871821325193308249847805 := by
  unfold tailWord_3645359
  simp only [CollatzResearch.WordTrace]
  refine ⟨132957165600494395596363131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88638110400329597064242087 132957165600494395596363131)
  ·
    refine ⟨199435748400741593394544697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132957165600494395596363131 199435748400741593394544697)
    ·
      refine ⟨149576811300556195045908523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199435748400741593394544697 149576811300556195045908523)
      ·
        refine ⟨224365216950834292568862785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149576811300556195045908523 224365216950834292568862785)
        ·
          refine ⟨168273912713125719426647089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224365216950834292568862785 168273912713125719426647089)
          ·
            refine ⟨126205434534844289569985317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168273912713125719426647089 126205434534844289569985317)
            ·
              refine ⟨23663518975283304294372247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126205434534844289569985317 23663518975283304294372247)
              ·
                refine ⟨35495278462924956441558371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23663518975283304294372247 35495278462924956441558371)
                ·
                  refine ⟨53242917694387434662337557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35495278462924956441558371 53242917694387434662337557)
                  ·
                    refine ⟨2495761766924410999797073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53242917694387434662337557 2495761766924410999797073)
                    ·
                      refine ⟨1871821325193308249847805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2495761766924410999797073 1871821325193308249847805)
                      ·
                        rfl

theorem cell23_3645359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 6, 2].length) (baseStart_3645359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645359 prefixEnd_3645359 := by exact prefixLift 3645359
  have htrace : WordTrace (prefixWord ++ tailWord_3645359) baseStart_3645359 baseEnd_3645359 := by
    simpa [prefixWord, tailWord_3645359, baseEnd_3645359] using wordTrace_append hprefix tailTrace_3645359
  have hstable : (prefixWord ++ tailWord_3645359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645359).length < 2 ^ (prefixWord ++ tailWord_3645359).sum := by decide
  have hdescent : baseEnd_3645359 < baseStart_3645359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645362 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_3645362 : Nat := 118140960795 + 3645362 * 2 ^ 59
def prefixEnd_3645362 : Nat := 4983230072969 + 3 ^ 40 * 3645362 * 2
def baseEnd_3645362 : Nat := 1871822865635271738110291

theorem tailTrace_3645362 : CollatzResearch.WordTrace tailWord_3645362 prefixEnd_3645362 1871822865635271738110291 := by
  unfold tailWord_3645362
  simp only [CollatzResearch.WordTrace]
  refine ⟨33239318754870881777180585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88638183346322351405814893 33239318754870881777180585)
  ·
    refine ⟨24929489066153161332885439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33239318754870881777180585 24929489066153161332885439)
    ·
      refine ⟨37394233599229741999328159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24929489066153161332885439 37394233599229741999328159)
      ·
        refine ⟨56091350398844612998992239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37394233599229741999328159 56091350398844612998992239)
        ·
          refine ⟨84137025598266919498488359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56091350398844612998992239 84137025598266919498488359)
          ·
            refine ⟨126205538397400379247732539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84137025598266919498488359 126205538397400379247732539)
            ·
              refine ⟨189308307596100568871598809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126205538397400379247732539 189308307596100568871598809)
              ·
                refine ⟨141981230697075426653699107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189308307596100568871598809 141981230697075426653699107)
                ·
                  refine ⟨212971846045613139980548661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141981230697075426653699107 212971846045613139980548661)
                  ·
                    refine ⟨19966110566776231873176437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 212971846045613139980548661 19966110566776231873176437)
                    ·
                      refine ⟨1871822865635271738110291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19966110566776231873176437 1871822865635271738110291)
                      ·
                        rfl

theorem cell23_3645362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_3645362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645362 prefixEnd_3645362 := by exact prefixLift 3645362
  have htrace : WordTrace (prefixWord ++ tailWord_3645362) baseStart_3645362 baseEnd_3645362 := by
    simpa [prefixWord, tailWord_3645362, baseEnd_3645362] using wordTrace_append hprefix tailTrace_3645362
  have hstable : (prefixWord ++ tailWord_3645362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645362).length < 2 ^ (prefixWord ++ tailWord_3645362).sum := by decide
  have hdescent : baseEnd_3645362 < baseStart_3645362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645369 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 5, 4]
def baseStart_3645369 : Nat := 118140960795 + 3645369 * 2 ^ 59
def prefixEnd_3645369 : Nat := 4983230072969 + 3 ^ 40 * 3645369 * 2
def baseEnd_3645369 : Nat := 623942153333284403574253

theorem tailTrace_3645369 : CollatzResearch.WordTrace tailWord_3645369 prefixEnd_3645369 623942153333284403574253 := by
  unfold tailWord_3645369
  simp only [CollatzResearch.WordTrace]
  refine ⟨132957530330458167304227161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88638353553638778202818107 132957530330458167304227161)
  ·
    refine ⟨99718147747843625478170371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132957530330458167304227161 99718147747843625478170371)
    ·
      refine ⟨149577221621765438217255557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99718147747843625478170371 149577221621765438217255557)
      ·
        refine ⟨28045729054081019665735417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149577221621765438217255557 28045729054081019665735417)
        ·
          refine ⟨21034296790560764749301563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28045729054081019665735417 21034296790560764749301563)
          ·
            refine ⟨31551445185841147123952345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21034296790560764749301563 31551445185841147123952345)
            ·
              refine ⟨23663583889380860342964259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31551445185841147123952345 23663583889380860342964259)
              ·
                refine ⟨35495375834071290514446389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23663583889380860342964259 35495375834071290514446389)
                ·
                  refine ⟨3327691484444183485729349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35495375834071290514446389 3327691484444183485729349)
                  ·
                    refine ⟨623942153333284403574253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3327691484444183485729349 623942153333284403574253)
                    ·
                      rfl

theorem cell23_3645369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 4].length) (baseStart_3645369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645369 prefixEnd_3645369 := by exact prefixLift 3645369
  have htrace : WordTrace (prefixWord ++ tailWord_3645369) baseStart_3645369 baseEnd_3645369 := by
    simpa [prefixWord, tailWord_3645369, baseEnd_3645369] using wordTrace_append hprefix tailTrace_3645369
  have hstable : (prefixWord ++ tailWord_3645369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645369).length < 2 ^ (prefixWord ++ tailWord_3645369).sum := by decide
  have hdescent : baseEnd_3645369 < baseStart_3645369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645396 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_3645396 : Nat := 118140960795 + 3645396 * 2 ^ 59
def prefixEnd_3645396 : Nat := 4983230072969 + 3 ^ 40 * 3645396 * 2
def baseEnd_3645396 : Nat := 1871840323977524605085135

theorem tailTrace_3645396 : CollatzResearch.WordTrace tailWord_3645396 prefixEnd_3645396 1871840323977524605085135 := by
  unfold tailWord_3645396
  simp only [CollatzResearch.WordTrace]
  refine ⟨66479257550680175457730021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88639010067573567276973361 66479257550680175457730021)
  ·
    refine ⟨12464860790752532898324379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66479257550680175457730021 12464860790752532898324379)
    ·
      refine ⟨18697291186128799347486569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12464860790752532898324379 18697291186128799347486569)
      ·
        refine ⟨14022968389596599510614927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18697291186128799347486569 14022968389596599510614927)
        ·
          refine ⟨21034452584394899265922391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14022968389596599510614927 21034452584394899265922391)
          ·
            refine ⟨31551678876592348898883587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21034452584394899265922391 31551678876592348898883587)
            ·
              refine ⟨47327518314888523348325381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31551678876592348898883587 47327518314888523348325381)
              ·
                refine ⟨8873909684041598127811009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47327518314888523348325381 8873909684041598127811009)
                ·
                  refine ⟨6655432263031198595858257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8873909684041598127811009 6655432263031198595858257)
                  ·
                    refine ⟨4991574197273398946893693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6655432263031198595858257 4991574197273398946893693)
                    ·
                      refine ⟨1871840323977524605085135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4991574197273398946893693 1871840323977524605085135)
                      ·
                        rfl

theorem cell23_3645396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_3645396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645396 prefixEnd_3645396 := by exact prefixLift 3645396
  have htrace : WordTrace (prefixWord ++ tailWord_3645396) baseStart_3645396 baseEnd_3645396 := by
    simpa [prefixWord, tailWord_3645396, baseEnd_3645396] using wordTrace_append hprefix tailTrace_3645396
  have hstable : (prefixWord ++ tailWord_3645396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645396).length < 2 ^ (prefixWord ++ tailWord_3645396).sum := by decide
  have hdescent : baseEnd_3645396 < baseStart_3645396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645399 : List Nat := [1, 1, 3, 2, 1, 1, 6, 2, 6]
def baseStart_3645399 : Nat := 118140960795 + 3645399 * 2 ^ 59
def prefixEnd_3645399 : Nat := 4983230072969 + 3 ^ 40 * 3645399 * 2
def baseEnd_3645399 : Nat := 207982429379943121483069

theorem tailTrace_3645399 : CollatzResearch.WordTrace tailWord_3645399 prefixEnd_3645399 207982429379943121483069 := by
  unfold tailWord_3645399
  simp only [CollatzResearch.WordTrace]
  refine ⟨132958624520349482427819251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88639083013566321618546167 132958624520349482427819251)
  ·
    refine ⟨199437936780524223641728877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132958624520349482427819251 199437936780524223641728877)
    ·
      refine ⟨74789226292696583865648329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199437936780524223641728877 74789226292696583865648329)
      ·
        refine ⟨56091919719522437899236247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74789226292696583865648329 56091919719522437899236247)
        ·
          refine ⟨84137879579283656848854371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56091919719522437899236247 84137879579283656848854371)
          ·
            refine ⟨126206819368925485273281557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84137879579283656848854371 126206819368925485273281557)
            ·
              refine ⟨5915944657918382122185073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126206819368925485273281557 5915944657918382122185073)
              ·
                refine ⟨4436958493438786591638805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5915944657918382122185073 4436958493438786591638805)
                ·
                  refine ⟨207982429379943121483069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4436958493438786591638805 207982429379943121483069)
                  ·
                    rfl

theorem cell23_3645399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 6].length) (baseStart_3645399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645399 prefixEnd_3645399 := by exact prefixLift 3645399
  have htrace : WordTrace (prefixWord ++ tailWord_3645399) baseStart_3645399 baseEnd_3645399 := by
    simpa [prefixWord, tailWord_3645399, baseEnd_3645399] using wordTrace_append hprefix tailTrace_3645399
  have hstable : (prefixWord ++ tailWord_3645399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645399).length < 2 ^ (prefixWord ++ tailWord_3645399).sum := by decide
  have hdescent : baseEnd_3645399 < baseStart_3645399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645410 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_3645410 : Nat := 118140960795 + 3645410 * 2 ^ 59
def prefixEnd_3645410 : Nat := 4983230072969 + 3 ^ 40 * 3645410 * 2
def baseEnd_3645410 : Nat := 1871847512706687550310071

theorem tailTrace_3645410 : CollatzResearch.WordTrace tailWord_3645410 prefixEnd_3645410 1871847512706687550310071 := by
  unfold tailWord_3645410
  simp only [CollatzResearch.WordTrace]
  refine ⟨33239756430827407826617421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88639350482206420870979789 33239756430827407826617421)
  ·
    refine ⟨12464908661560277934981533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33239756430827407826617421 12464908661560277934981533)
    ·
      refine ⟨4674340748085104225618075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12464908661560277934981533 4674340748085104225618075)
      ·
        refine ⟨7011511122127656338427113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4674340748085104225618075 7011511122127656338427113)
        ·
          refine ⟨5258633341595742253820335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7011511122127656338427113 5258633341595742253820335)
          ·
            refine ⟨7887950012393613380730503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5258633341595742253820335 7887950012393613380730503)
            ·
              refine ⟨11831925018590420071095755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7887950012393613380730503 11831925018590420071095755)
              ·
                refine ⟨17747887527885630106643633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11831925018590420071095755 17747887527885630106643633)
                ·
                  refine ⟨13310915645914222579982725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17747887527885630106643633 13310915645914222579982725)
                  ·
                    refine ⟨2495796683608916733746761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13310915645914222579982725 2495796683608916733746761)
                    ·
                      refine ⟨1871847512706687550310071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2495796683608916733746761 1871847512706687550310071)
                      ·
                        rfl

theorem cell23_3645410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_3645410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645410 prefixEnd_3645410 := by exact prefixLift 3645410
  have htrace : WordTrace (prefixWord ++ tailWord_3645410) baseStart_3645410 baseEnd_3645410 := by
    simpa [prefixWord, tailWord_3645410, baseEnd_3645410] using wordTrace_append hprefix tailTrace_3645410
  have hstable : (prefixWord ++ tailWord_3645410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645410).length < 2 ^ (prefixWord ++ tailWord_3645410).sum := by decide
  have hdescent : baseEnd_3645410 < baseStart_3645410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645430 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_3645430 : Nat := 118140960795 + 3645430 * 2 ^ 59
def prefixEnd_3645430 : Nat := 4983230072969 + 3 ^ 40 * 3645430 * 2
def baseEnd_3645430 : Nat := 1871857782319777472059979

theorem tailTrace_3645430 : CollatzResearch.WordTrace tailWord_3645430 prefixEnd_3645430 1871857782319777472059979 := by
  unfold tailWord_3645430
  simp only [CollatzResearch.WordTrace]
  refine ⟨8309984698952323420137359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88639836788824783148131829 8309984698952323420137359)
  ·
    refine ⟨12464977048428485130206039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8309984698952323420137359 12464977048428485130206039)
    ·
      refine ⟨18697465572642727695309059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12464977048428485130206039 18697465572642727695309059)
      ·
        refine ⟨28046198358964091542963589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18697465572642727695309059 28046198358964091542963589)
        ·
          refine ⟨5258662192305767164305673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28046198358964091542963589 5258662192305767164305673)
          ·
            refine ⟨3943996644229325373229255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5258662192305767164305673 3943996644229325373229255)
            ·
              refine ⟨5915994966343988059843883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3943996644229325373229255 5915994966343988059843883)
              ·
                refine ⟨8873992449515982089765825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5915994966343988059843883 8873992449515982089765825)
                ·
                  refine ⟨6655494337136986567324369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8873992449515982089765825 6655494337136986567324369)
                  ·
                    refine ⟨4991620752852739925493277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6655494337136986567324369 4991620752852739925493277)
                    ·
                      refine ⟨1871857782319777472059979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4991620752852739925493277 1871857782319777472059979)
                      ·
                        rfl

theorem cell23_3645430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_3645430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645430 prefixEnd_3645430 := by exact prefixLift 3645430
  have htrace : WordTrace (prefixWord ++ tailWord_3645430) baseStart_3645430 baseEnd_3645430 := by
    simpa [prefixWord, tailWord_3645430, baseEnd_3645430] using wordTrace_append hprefix tailTrace_3645430
  have hstable : (prefixWord ++ tailWord_3645430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645430).length < 2 ^ (prefixWord ++ tailWord_3645430).sum := by decide
  have hdescent : baseEnd_3645430 < baseStart_3645430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645436 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 1, 5, 2]
def baseStart_3645436 : Nat := 118140960795 + 3645436 * 2 ^ 59
def prefixEnd_3645436 : Nat := 4983230072969 + 3 ^ 40 * 3645436 * 2
def baseEnd_3645436 : Nat := 1871860863203704448584951

theorem tailTrace_3645436 : CollatzResearch.WordTrace tailWord_3645436 prefixEnd_3645436 1871860863203704448584951 := by
  unfold tailWord_3645436
  simp only [CollatzResearch.WordTrace]
  refine ⟨66479987010607718873458081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88639982680810291831277441 66479987010607718873458081)
  ·
    refine ⟨49859990257955789155093561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66479987010607718873458081 49859990257955789155093561)
    ·
      refine ⟨37394992693466841866320171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49859990257955789155093561 37394992693466841866320171)
      ·
        refine ⟨56092489040200262799480257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37394992693466841866320171 56092489040200262799480257)
        ·
          refine ⟨42069366780150197099610193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56092489040200262799480257 42069366780150197099610193)
          ·
            refine ⟨31552025085112647824707645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42069366780150197099610193 31552025085112647824707645)
            ·
              refine ⟨11832009406917242934265367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31552025085112647824707645 11832009406917242934265367)
              ·
                refine ⟨17748014110375864401398051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11832009406917242934265367 17748014110375864401398051)
                ·
                  refine ⟨26622021165563796602097077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17748014110375864401398051 26622021165563796602097077)
                  ·
                    refine ⟨2495814484271605931446601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26622021165563796602097077 2495814484271605931446601)
                    ·
                      refine ⟨1871860863203704448584951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2495814484271605931446601 1871860863203704448584951)
                      ·
                        rfl

theorem cell23_3645436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_3645436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645436 prefixEnd_3645436 := by exact prefixLift 3645436
  have htrace : WordTrace (prefixWord ++ tailWord_3645436) baseStart_3645436 baseEnd_3645436 := by
    simpa [prefixWord, tailWord_3645436, baseEnd_3645436] using wordTrace_append hprefix tailTrace_3645436
  have hstable : (prefixWord ++ tailWord_3645436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645436).length < 2 ^ (prefixWord ++ tailWord_3645436).sum := by decide
  have hdescent : baseEnd_3645436 < baseStart_3645436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645480 : List Nat := [2, 1, 5, 3, 1, 1, 2, 2, 1, 5]
def baseStart_3645480 : Nat := 118140960795 + 3645480 * 2 ^ 59
def prefixEnd_3645480 : Nat := 4983230072969 + 3 ^ 40 * 3645480 * 2
def baseEnd_3645480 : Nat := 623961152117500758811583

theorem tailTrace_3645480 : CollatzResearch.WordTrace tailWord_3645480 prefixEnd_3645480 623961152117500758811583 := by
  unfold tailWord_3645480
  simp only [CollatzResearch.WordTrace]
  refine ⟨66480789416528016630758947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88641052555370688841011929 66480789416528016630758947)
  ·
    refine ⟨99721184124792024946138421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66480789416528016630758947 99721184124792024946138421)
    ·
      refine ⟨9348861011699252338700477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99721184124792024946138421 9348861011699252338700477)
      ·
        refine ⟨3505822879387219627012679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9348861011699252338700477 3505822879387219627012679)
        ·
          refine ⟨5258734319080829440519019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3505822879387219627012679 5258734319080829440519019)
          ·
            refine ⟨7888101478621244160778529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5258734319080829440519019 7888101478621244160778529)
            ·
              refine ⟨5916076108965933120583897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7888101478621244160778529 5916076108965933120583897)
              ·
                refine ⟨4437057081724449840437923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5916076108965933120583897 4437057081724449840437923)
                ·
                  refine ⟨6655585622586674760656885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4437057081724449840437923 6655585622586674760656885)
                  ·
                    refine ⟨623961152117500758811583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6655585622586674760656885 623961152117500758811583)
                    ·
                      rfl

theorem cell23_3645480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_3645480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645480 prefixEnd_3645480 := by exact prefixLift 3645480
  have htrace : WordTrace (prefixWord ++ tailWord_3645480) baseStart_3645480 baseEnd_3645480 := by
    simpa [prefixWord, tailWord_3645480, baseEnd_3645480] using wordTrace_append hprefix tailTrace_3645480
  have hstable : (prefixWord ++ tailWord_3645480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645480).length < 2 ^ (prefixWord ++ tailWord_3645480).sum := by decide
  have hdescent : baseEnd_3645480 < baseStart_3645480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645489 : List Nat := [1, 2, 2, 3, 1, 4, 1, 9]
def baseStart_3645489 : Nat := 118140960795 + 3645489 * 2 ^ 59
def prefixEnd_3645489 : Nat := 4983230072969 + 3 ^ 40 * 3645489 * 2
def baseEnd_3645489 : Nat := 69329188062162694119341

theorem tailTrace_3645489 : CollatzResearch.WordTrace tailWord_3645489 prefixEnd_3645489 69329188062162694119341 := by
  unfold tailWord_3645489
  simp only [CollatzResearch.WordTrace]
  refine ⟨132961907090023427798595521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88641271393348951865730347 132961907090023427798595521)
  ·
    refine ⟨99721430317517570848946641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132961907090023427798595521 99721430317517570848946641)
    ·
      refine ⟨74791072738138178136709981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99721430317517570848946641 74791072738138178136709981)
      ·
        refine ⟨28046652276801816801266243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74791072738138178136709981 28046652276801816801266243)
        ·
          refine ⟨42069978415202725201899365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28046652276801816801266243 42069978415202725201899365)
          ·
            refine ⟨7888120952850510975356131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42069978415202725201899365 7888120952850510975356131)
            ·
              refine ⟨11832181429275766463034197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7888120952850510975356131 11832181429275766463034197)
              ·
                refine ⟨69329188062162694119341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11832181429275766463034197 69329188062162694119341)
                ·
                  rfl

theorem cell23_3645489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 9].length) (baseStart_3645489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645489 prefixEnd_3645489 := by exact prefixLift 3645489
  have htrace : WordTrace (prefixWord ++ tailWord_3645489) baseStart_3645489 baseEnd_3645489 := by
    simpa [prefixWord, tailWord_3645489, baseEnd_3645489] using wordTrace_append hprefix tailTrace_3645489
  have hstable : (prefixWord ++ tailWord_3645489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645489).length < 2 ^ (prefixWord ++ tailWord_3645489).sum := by decide
  have hdescent : baseEnd_3645489 < baseStart_3645489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645510 : List Nat := [6, 1, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_3645510 : Nat := 118140960795 + 3645510 * 2 ^ 59
def prefixEnd_3645510 : Nat := 4983230072969 + 3 ^ 40 * 3645510 * 2
def baseEnd_3645510 : Nat := 623966286924045719686537

theorem tailTrace_3645510 : CollatzResearch.WordTrace tailWord_3645510 prefixEnd_3645510 623966286924045719686537 := by
  unfold tailWord_3645510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4155083531967104637034687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88641782015298232256739989 4155083531967104637034687)
  ·
    refine ⟨6232625297950656955552031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4155083531967104637034687 6232625297950656955552031)
    ·
      refine ⟨9348937946925985433328047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6232625297950656955552031 9348937946925985433328047)
      ·
        refine ⟨14023406920388978149992071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9348937946925985433328047 14023406920388978149992071)
        ·
          refine ⟨21035110380583467224988107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14023406920388978149992071 21035110380583467224988107)
          ·
            refine ⟨31552665570875200837482161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21035110380583467224988107 31552665570875200837482161)
            ·
              refine ⟨23664499178156400628111621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31552665570875200837482161 23664499178156400628111621)
              ·
                refine ⟨4437093595904325117770929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23664499178156400628111621 4437093595904325117770929)
                ·
                  refine ⟨3327820196928243838328197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4437093595904325117770929 3327820196928243838328197)
                  ·
                    refine ⟨623966286924045719686537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3327820196928243838328197 623966286924045719686537)
                    ·
                      rfl

theorem cell23_3645510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_3645510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645510 prefixEnd_3645510 := by exact prefixLift 3645510
  have htrace : WordTrace (prefixWord ++ tailWord_3645510) baseStart_3645510 baseEnd_3645510 := by
    simpa [prefixWord, tailWord_3645510, baseEnd_3645510] using wordTrace_append hprefix tailTrace_3645510
  have hstable : (prefixWord ++ tailWord_3645510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645510).length < 2 ^ (prefixWord ++ tailWord_3645510).sum := by decide
  have hdescent : baseEnd_3645510 < baseStart_3645510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645534 : List Nat := [4, 4, 1, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_3645534 : Nat := 118140960795 + 3645534 * 2 ^ 59
def prefixEnd_3645534 : Nat := 4983230072969 + 3 ^ 40 * 3645534 * 2
def baseEnd_3645534 : Nat := 1871911184307845065159501

theorem tailTrace_3645534 : CollatzResearch.WordTrace tailWord_3645534 prefixEnd_3645534 1871911184307845065159501 := by
  unfold tailWord_3645534
  simp only [CollatzResearch.WordTrace]
  refine ⟨16620443546857550060497957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88642365583240266989322437 16620443546857550060497957)
  ·
    refine ⟨3116333165035790636343367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16620443546857550060497957 3116333165035790636343367)
    ·
      refine ⟨4674499747553685954515051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3116333165035790636343367 4674499747553685954515051)
      ·
        refine ⟨7011749621330528931772577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4674499747553685954515051 7011749621330528931772577)
        ·
          refine ⟨5258812215997896698829433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7011749621330528931772577 5258812215997896698829433)
          ·
            refine ⟨3944109161998422524122075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5258812215997896698829433 3944109161998422524122075)
            ·
              refine ⟨5916163742997633786183113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944109161998422524122075 5916163742997633786183113)
              ·
                refine ⟨4437122807248225339637335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5916163742997633786183113 4437122807248225339637335)
                ·
                  refine ⟨6655684210872338009456003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4437122807248225339637335 6655684210872338009456003)
                  ·
                    refine ⟨9983526316308507014184005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6655684210872338009456003 9983526316308507014184005)
                    ·
                      refine ⟨1871911184307845065159501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9983526316308507014184005 1871911184307845065159501)
                      ·
                        rfl

theorem cell23_3645534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_3645534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645534 prefixEnd_3645534 := by exact prefixLift 3645534
  have htrace : WordTrace (prefixWord ++ tailWord_3645534) baseStart_3645534 baseEnd_3645534 := by
    simpa [prefixWord, tailWord_3645534, baseEnd_3645534] using wordTrace_append hprefix tailTrace_3645534
  have hstable : (prefixWord ++ tailWord_3645534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645534).length < 2 ^ (prefixWord ++ tailWord_3645534).sum := by decide
  have hdescent : baseEnd_3645534 < baseStart_3645534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645543 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_3645543 : Nat := 118140960795 + 3645543 * 2 ^ 59
def prefixEnd_3645543 : Nat := 4983230072969 + 3 ^ 40 * 3645543 * 2
def baseEnd_3645543 : Nat := 1871915805633735529946959

theorem tailTrace_3645543 : CollatzResearch.WordTrace tailWord_3645543 prefixEnd_3645543 1871915805633735529946959 := by
  unfold tailWord_3645543
  simp only [CollatzResearch.WordTrace]
  refine ⟨132963876631827795021061283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88642584421218530014040855 132963876631827795021061283)
  ·
    refine ⟨199445814947741692531591925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132963876631827795021061283 199445814947741692531591925)
    ·
      refine ⟨18698045151350783674836743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199445814947741692531591925 18698045151350783674836743)
      ·
        refine ⟨28047067727026175512255115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18698045151350783674836743 28047067727026175512255115)
        ·
          refine ⟨42070601590539263268382673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28047067727026175512255115 42070601590539263268382673)
          ·
            refine ⟨31552951192904447451287005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42070601590539263268382673 31552951192904447451287005)
            ·
              refine ⟨11832356697339167794232627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31552951192904447451287005 11832356697339167794232627)
              ·
                refine ⟨17748535046008751691348941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11832356697339167794232627 17748535046008751691348941)
                ·
                  refine ⟨6655700642253281884255853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17748535046008751691348941 6655700642253281884255853)
                  ·
                    refine ⟨2495887740844980706595945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6655700642253281884255853 2495887740844980706595945)
                    ·
                      refine ⟨1871915805633735529946959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2495887740844980706595945 1871915805633735529946959)
                      ·
                        rfl

theorem cell23_3645543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_3645543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645543 prefixEnd_3645543 := by exact prefixLift 3645543
  have htrace : WordTrace (prefixWord ++ tailWord_3645543) baseStart_3645543 baseEnd_3645543 := by
    simpa [prefixWord, tailWord_3645543, baseEnd_3645543] using wordTrace_append hprefix tailTrace_3645543
  have hstable : (prefixWord ++ tailWord_3645543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645543).length < 2 ^ (prefixWord ++ tailWord_3645543).sum := by decide
  have hdescent : baseEnd_3645543 < baseStart_3645543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645596 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 7]
def baseStart_3645596 : Nat := 118140960795 + 3645596 * 2 ^ 59
def prefixEnd_3645596 : Nat := 4983230072969 + 3 ^ 40 * 3645596 * 2
def baseEnd_3645596 : Nat := 207993668900935980287135

theorem tailTrace_3645596 : CollatzResearch.WordTrace tailWord_3645596 prefixEnd_3645596 207993668900935980287135 := by
  unfold tailWord_3645596
  simp only [CollatzResearch.WordTrace]
  refine ⟨66482904850317892536370321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88643873133757190048493761 66482904850317892536370321)
  ·
    refine ⟨49862178637738419402277741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66482904850317892536370321 49862178637738419402277741)
    ·
      refine ⟨18698316989151907275854153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49862178637738419402277741 18698316989151907275854153)
      ·
        refine ⟨14023737741863930456890615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18698316989151907275854153 14023737741863930456890615)
        ·
          refine ⟨21035606612795895685335923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14023737741863930456890615 21035606612795895685335923)
          ·
            refine ⟨31553409919193843528003885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21035606612795895685335923 31553409919193843528003885)
            ·
              refine ⟨11832528719697691323001457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31553409919193843528003885 11832528719697691323001457)
              ·
                refine ⟨8874396539773268492251093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11832528719697691323001457 8874396539773268492251093)
                ·
                  refine ⟨207993668900935980287135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8874396539773268492251093 207993668900935980287135)
                  ·
                    rfl

theorem cell23_3645596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 7].length) (baseStart_3645596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645596 prefixEnd_3645596 := by exact prefixLift 3645596
  have htrace : WordTrace (prefixWord ++ tailWord_3645596) baseStart_3645596 baseEnd_3645596 := by
    simpa [prefixWord, tailWord_3645596, baseEnd_3645596] using wordTrace_append hprefix tailTrace_3645596
  have hstable : (prefixWord ++ tailWord_3645596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645596).length < 2 ^ (prefixWord ++ tailWord_3645596).sum := by decide
  have hdescent : baseEnd_3645596 < baseStart_3645596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645626 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 2, 5]
def baseStart_3645626 : Nat := 118140960795 + 3645626 * 2 ^ 59
def prefixEnd_3645626 : Nat := 4983230072969 + 3 ^ 40 * 3645626 * 2
def baseEnd_3645626 : Nat := 623986141509352901736359

theorem tailTrace_3645626 : CollatzResearch.WordTrace tailWord_3645626 prefixEnd_3645626 623986141509352901736359 := by
  unfold tailWord_3645626
  simp only [CollatzResearch.WordTrace]
  refine ⟨33241725972631775049083183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88644602593684733464221821 33241725972631775049083183)
  ·
    refine ⟨49862588958947662573624775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33241725972631775049083183 49862588958947662573624775)
    ·
      refine ⟨74793883438421493860437163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49862588958947662573624775 74793883438421493860437163)
      ·
        refine ⟨112190825157632240790655745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74793883438421493860437163 112190825157632240790655745)
        ·
          refine ⟨84143118868224180592991809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112190825157632240790655745 84143118868224180592991809)
          ·
            refine ⟨63107339151168135444743857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84143118868224180592991809 63107339151168135444743857)
            ·
              refine ⟨47330504363376101583557893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63107339151168135444743857 47330504363376101583557893)
              ·
                refine ⟨8874469568133019046917105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47330504363376101583557893 8874469568133019046917105)
                ·
                  refine ⟨6655852176099764285187829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8874469568133019046917105 6655852176099764285187829)
                  ·
                    refine ⟨623986141509352901736359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6655852176099764285187829 623986141509352901736359)
                    ·
                      rfl

theorem cell23_3645626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_3645626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645626 prefixEnd_3645626 := by exact prefixLift 3645626
  have htrace : WordTrace (prefixWord ++ tailWord_3645626) baseStart_3645626 baseEnd_3645626 := by
    simpa [prefixWord, tailWord_3645626, baseEnd_3645626] using wordTrace_append hprefix tailTrace_3645626
  have hstable : (prefixWord ++ tailWord_3645626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645626).length < 2 ^ (prefixWord ++ tailWord_3645626).sum := by decide
  have hdescent : baseEnd_3645626 < baseStart_3645626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645683 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 3]
def baseStart_3645683 : Nat := 118140960795 + 3645683 * 2 ^ 59
def prefixEnd_3645683 : Nat := 4983230072969 + 3 ^ 40 * 3645683 * 2
def baseEnd_3645683 : Nat := 1871987692925364982196315

theorem tailTrace_3645683 : CollatzResearch.WordTrace tailWord_3645683 prefixEnd_3645683 1871987692925364982196315 := by
  unfold tailWord_3645683
  simp only [CollatzResearch.WordTrace]
  refine ⟨132968982851320598931157703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88645988567547065954105135 132968982851320598931157703)
  ·
    refine ⟨199453474276980898396736555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132968982851320598931157703 199453474276980898396736555)
    ·
      refine ⟨299180211415471347595104833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199453474276980898396736555 299180211415471347595104833)
      ·
        refine ⟨224385158561603510696328625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299180211415471347595104833 224385158561603510696328625)
        ·
          refine ⟨168288868921202633022246469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224385158561603510696328625 168288868921202633022246469)
          ·
            refine ⟨31554162922725493691671213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168288868921202633022246469 31554162922725493691671213)
            ·
              refine ⟨11832811096022060134376705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31554162922725493691671213 11832811096022060134376705)
              ·
                refine ⟨8874608322016545100782529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11832811096022060134376705 8874608322016545100782529)
                ·
                  refine ⟨6655956241512408825586897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8874608322016545100782529 6655956241512408825586897)
                  ·
                    refine ⟨4991967181134306619190173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6655956241512408825586897 4991967181134306619190173)
                    ·
                      refine ⟨1871987692925364982196315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4991967181134306619190173 1871987692925364982196315)
                      ·
                        rfl

theorem cell23_3645683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 3].length) (baseStart_3645683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645683 prefixEnd_3645683 := by exact prefixLift 3645683
  have htrace : WordTrace (prefixWord ++ tailWord_3645683) baseStart_3645683 baseEnd_3645683 := by
    simpa [prefixWord, tailWord_3645683, baseEnd_3645683] using wordTrace_append hprefix tailTrace_3645683
  have hstable : (prefixWord ++ tailWord_3645683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645683).length < 2 ^ (prefixWord ++ tailWord_3645683).sum := by decide
  have hdescent : baseEnd_3645683 < baseStart_3645683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645690 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 3, 4]
def baseStart_3645690 : Nat := 118140960795 + 3645690 * 2 ^ 59
def prefixEnd_3645690 : Nat := 4983230072969 + 3 ^ 40 * 3645690 * 2
def baseEnd_3645690 : Nat := 623997095763315484936261

theorem tailTrace_3645690 : CollatzResearch.WordTrace tailWord_3645690 prefixEnd_3645690 623997095763315484936261 := by
  unfold tailWord_3645690
  simp only [CollatzResearch.WordTrace]
  refine ⟨33242309540573809781665631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88646158774863492751108349 33242309540573809781665631)
  ·
    refine ⟨49863464310860714672498447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33242309540573809781665631 49863464310860714672498447)
    ·
      refine ⟨74795196466291072008747671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49863464310860714672498447 74795196466291072008747671)
      ·
        refine ⟨112192794699436608013121507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74795196466291072008747671 112192794699436608013121507)
        ·
          refine ⟨168289192049154912019682261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112192794699436608013121507 168289192049154912019682261)
          ·
            refine ⟨3944277938652068250461303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 168289192049154912019682261 3944277938652068250461303)
            ·
              refine ⟨5916416907978102375691955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944277938652068250461303 5916416907978102375691955)
              ·
                refine ⟨8874625361967153563537933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916416907978102375691955 8874625361967153563537933)
                ·
                  refine ⟨3327984510737682586326725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8874625361967153563537933 3327984510737682586326725)
                  ·
                    refine ⟨623997095763315484936261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3327984510737682586326725 623997095763315484936261)
                    ·
                      rfl

theorem cell23_3645690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_3645690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645690 prefixEnd_3645690 := by exact prefixLift 3645690
  have htrace : WordTrace (prefixWord ++ tailWord_3645690) baseStart_3645690 baseEnd_3645690 := by
    simpa [prefixWord, tailWord_3645690, baseEnd_3645690] using wordTrace_append hprefix tailTrace_3645690
  have hstable : (prefixWord ++ tailWord_3645690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645690).length < 2 ^ (prefixWord ++ tailWord_3645690).sum := by decide
  have hdescent : baseEnd_3645690 < baseStart_3645690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645706 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_3645706 : Nat := 118140960795 + 3645706 * 2 ^ 59
def prefixEnd_3645706 : Nat := 4983230072969 + 3 ^ 40 * 3645706 * 2
def baseEnd_3645706 : Nat := 1871999502980418392208709

theorem tailTrace_3645706 : CollatzResearch.WordTrace tailWord_3645706 prefixEnd_3645706 1871999502980418392208709 := by
  unfold tailWord_3645706
  simp only [CollatzResearch.WordTrace]
  refine ⟨33242455432559318464811243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88646547820158182572829981 33242455432559318464811243)
  ·
    refine ⟨49863683148838977697216865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33242455432559318464811243 49863683148838977697216865)
    ·
      refine ⟨37397762361629233272912649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49863683148838977697216865 37397762361629233272912649)
      ·
        refine ⟨28048321771221924954684487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37397762361629233272912649 28048321771221924954684487)
        ·
          refine ⟨42072482656832887432026731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28048321771221924954684487 42072482656832887432026731)
          ·
            refine ⟨63108723985249331148040097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42072482656832887432026731 63108723985249331148040097)
            ·
              refine ⟨47331542988936998361030073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63108723985249331148040097 47331542988936998361030073)
              ·
                refine ⟨35498657241702748770772555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47331542988936998361030073 35498657241702748770772555)
                ·
                  refine ⟨53247985862554123156158833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35498657241702748770772555 53247985862554123156158833)
                  ·
                    refine ⟨39935989396915592367119125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53247985862554123156158833 39935989396915592367119125)
                    ·
                      refine ⟨1871999502980418392208709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39935989396915592367119125 1871999502980418392208709)
                      ·
                        rfl

theorem cell23_3645706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_3645706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645706 prefixEnd_3645706 := by exact prefixLift 3645706
  have htrace : WordTrace (prefixWord ++ tailWord_3645706) baseStart_3645706 baseEnd_3645706 := by
    simpa [prefixWord, tailWord_3645706, baseEnd_3645706] using wordTrace_append hprefix tailTrace_3645706
  have hstable : (prefixWord ++ tailWord_3645706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645706).length < 2 ^ (prefixWord ++ tailWord_3645706).sum := by decide
  have hdescent : baseEnd_3645706 < baseStart_3645706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645723 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 1, 5, 2]
def baseStart_3645723 : Nat := 118140960795 + 3645723 * 2 ^ 59
def prefixEnd_3645723 : Nat := 4983230072969 + 3 ^ 40 * 3645723 * 2
def baseEnd_3645723 : Nat := 1872008232151544825696131

theorem tailTrace_3645723 : CollatzResearch.WordTrace tailWord_3645723 prefixEnd_3645723 1872008232151544825696131 := by
  unfold tailWord_3645723
  simp only [CollatzResearch.WordTrace]
  refine ⟨132970441771175685762613823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88646961180783790508409215 132970441771175685762613823)
  ·
    refine ⟨199455662656763528643920735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132970441771175685762613823 199455662656763528643920735)
    ·
      refine ⟨299183493985145292965881103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199455662656763528643920735 299183493985145292965881103)
      ·
        refine ⟨448775240977717939448821655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299183493985145292965881103 448775240977717939448821655)
        ·
          refine ⟨673162861466576909173232483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448775240977717939448821655 673162861466576909173232483)
          ·
            refine ⟨1009744292199865363759848725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673162861466576909173232483 1009744292199865363759848725)
            ·
              refine ⟨47331763696868688926242909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1009744292199865363759848725 47331763696868688926242909)
              ·
                refine ⟨17749411386325758347341091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47331763696868688926242909 17749411386325758347341091)
                ·
                  refine ⟨26624117079488637521011637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17749411386325758347341091 26624117079488637521011637)
                  ·
                    refine ⟨2496010976202059767594841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26624117079488637521011637 2496010976202059767594841)
                    ·
                      refine ⟨1872008232151544825696131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496010976202059767594841 1872008232151544825696131)
                      ·
                        rfl

theorem cell23_3645723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 5, 2].length) (baseStart_3645723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645723 prefixEnd_3645723 := by exact prefixLift 3645723
  have htrace : WordTrace (prefixWord ++ tailWord_3645723) baseStart_3645723 baseEnd_3645723 := by
    simpa [prefixWord, tailWord_3645723, baseEnd_3645723] using wordTrace_append hprefix tailTrace_3645723
  have hstable : (prefixWord ++ tailWord_3645723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645723).length < 2 ^ (prefixWord ++ tailWord_3645723).sum := by decide
  have hdescent : baseEnd_3645723 < baseStart_3645723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645740 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 2, 3, 2]
def baseStart_3645740 : Nat := 118140960795 + 3645740 * 2 ^ 59
def prefixEnd_3645740 : Nat := 4983230072969 + 3 ^ 40 * 3645740 * 2
def baseEnd_3645740 : Nat := 1872016961322671259183553

theorem tailTrace_3645740 : CollatzResearch.WordTrace tailWord_3645740 prefixEnd_3645740 1872016961322671259183553 := by
  unfold tailWord_3645740
  simp only [CollatzResearch.WordTrace]
  refine ⟨66485530906057048832991337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88647374541409398443988449 66485530906057048832991337)
  ·
    refine ⟨49864148179542786624743503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66485530906057048832991337 49864148179542786624743503)
    ·
      refine ⟨74796222269314179937115255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49864148179542786624743503 74796222269314179937115255)
      ·
        refine ⟨112194333403971269905672883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74796222269314179937115255 112194333403971269905672883)
        ·
          refine ⟨168291500105956904858509325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112194333403971269905672883 168291500105956904858509325)
          ·
            refine ⟨63109312539733839321940997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168291500105956904858509325 63109312539733839321940997)
            ·
              refine ⟨11832996101200094872863937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63109312539733839321940997 11832996101200094872863937)
              ·
                refine ⟨8874747075900071154647953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11832996101200094872863937 8874747075900071154647953)
                ·
                  refine ⟨6656060306925053365985965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8874747075900071154647953 6656060306925053365985965)
                  ·
                    refine ⟨2496022615096895012244737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6656060306925053365985965 2496022615096895012244737)
                    ·
                      refine ⟨1872016961322671259183553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496022615096895012244737 1872016961322671259183553)
                      ·
                        rfl

theorem cell23_3645740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 3, 2].length) (baseStart_3645740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645740 prefixEnd_3645740 := by exact prefixLift 3645740
  have htrace : WordTrace (prefixWord ++ tailWord_3645740) baseStart_3645740 baseEnd_3645740 := by
    simpa [prefixWord, tailWord_3645740, baseEnd_3645740] using wordTrace_append hprefix tailTrace_3645740
  have hstable : (prefixWord ++ tailWord_3645740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645740).length < 2 ^ (prefixWord ++ tailWord_3645740).sum := by decide
  have hdescent : baseEnd_3645740 < baseStart_3645740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645747 : List Nat := [1, 1, 1, 2, 5, 1, 3, 4, 1, 1, 3]
def baseStart_3645747 : Nat := 118140960795 + 3645747 * 2 ^ 59
def prefixEnd_3645747 : Nat := 4983230072969 + 3 ^ 40 * 3645747 * 2
def baseEnd_3645747 : Nat := 1872020555687252731796021

theorem tailTrace_3645747 : CollatzResearch.WordTrace tailWord_3645747 prefixEnd_3645747 1872020555687252731796021 := by
  unfold tailWord_3645747
  simp only [CollatzResearch.WordTrace]
  refine ⟨132971317123088737861487495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88647544748725825240991663 132971317123088737861487495)
  ·
    refine ⟨199456975684633106792231243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132971317123088737861487495 199456975684633106792231243)
    ·
      refine ⟨299185463526949660188346865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199456975684633106792231243 299185463526949660188346865)
      ·
        refine ⟨224389097645212245141260149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299185463526949660188346865 224389097645212245141260149)
        ·
          refine ⟨21036477904238647981993139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224389097645212245141260149 21036477904238647981993139)
          ·
            refine ⟨31554716856357971972989709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21036477904238647981993139 31554716856357971972989709)
            ·
              refine ⟨11833018821134239489871141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31554716856357971972989709 11833018821134239489871141)
              ·
                refine ⟨2218691028962669904350839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11833018821134239489871141 2218691028962669904350839)
                ·
                  refine ⟨3328036543444004856526259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218691028962669904350839 3328036543444004856526259)
                  ·
                    refine ⟨4992054815166007284789389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3328036543444004856526259 4992054815166007284789389)
                    ·
                      refine ⟨1872020555687252731796021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4992054815166007284789389 1872020555687252731796021)
                      ·
                        rfl

theorem cell23_3645747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 1, 1, 3].length) (baseStart_3645747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645747 prefixEnd_3645747 := by exact prefixLift 3645747
  have htrace : WordTrace (prefixWord ++ tailWord_3645747) baseStart_3645747 baseEnd_3645747 := by
    simpa [prefixWord, tailWord_3645747, baseEnd_3645747] using wordTrace_append hprefix tailTrace_3645747
  have hstable : (prefixWord ++ tailWord_3645747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645747).length < 2 ^ (prefixWord ++ tailWord_3645747).sum := by decide
  have hdescent : baseEnd_3645747 < baseStart_3645747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645764 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3645764 : Nat := 118140960795 + 3645764 * 2 ^ 59
def prefixEnd_3645764 : Nat := 4983230072969 + 3 ^ 40 * 3645764 * 2
def baseEnd_3645764 : Nat := 1872029284858379165283443

theorem tailTrace_3645764 : CollatzResearch.WordTrace tailWord_3645764 prefixEnd_3645764 1872029284858379165283443 := by
  unfold tailWord_3645764
  simp only [CollatzResearch.WordTrace]
  refine ⟨66485968582013574882428173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88647958109351433176570897 66485968582013574882428173)
  ·
    refine ⟨24932238218255090580910565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66485968582013574882428173 24932238218255090580910565)
    ·
      refine ⟨4674794665922829483920731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24932238218255090580910565 4674794665922829483920731)
      ·
        refine ⟨7012191998884244225881097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4674794665922829483920731 7012191998884244225881097)
        ·
          refine ⟨5259143999163183169410823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7012191998884244225881097 5259143999163183169410823)
          ·
            refine ⟨7888715998744774754116235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5259143999163183169410823 7888715998744774754116235)
            ·
              refine ⟨11833073998117162131174353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7888715998744774754116235 11833073998117162131174353)
              ·
                refine ⟨8874805498587871598380765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11833073998117162131174353 8874805498587871598380765)
                ·
                  refine ⟨3328052061970451849392787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8874805498587871598380765 3328052061970451849392787)
                  ·
                    refine ⟨4992078092955677774089181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3328052061970451849392787 4992078092955677774089181)
                    ·
                      refine ⟨1872029284858379165283443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4992078092955677774089181 1872029284858379165283443)
                      ·
                        rfl

theorem cell23_3645764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3645764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645764 prefixEnd_3645764 := by exact prefixLift 3645764
  have htrace : WordTrace (prefixWord ++ tailWord_3645764) baseStart_3645764 baseEnd_3645764 := by
    simpa [prefixWord, tailWord_3645764, baseEnd_3645764] using wordTrace_append hprefix tailTrace_3645764
  have hstable : (prefixWord ++ tailWord_3645764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645764).length < 2 ^ (prefixWord ++ tailWord_3645764).sum := by decide
  have hdescent : baseEnd_3645764 < baseStart_3645764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645783 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_3645783 : Nat := 118140960795 + 3645783 * 2 ^ 59
def prefixEnd_3645783 : Nat := 4983230072969 + 3 ^ 40 * 3645783 * 2
def baseEnd_3645783 : Nat := 1872039040990814590945855

theorem tailTrace_3645783 : CollatzResearch.WordTrace tailWord_3645783 prefixEnd_3645783 1872039040990814590945855 := by
  unfold tailWord_3645783
  simp only [CollatzResearch.WordTrace]
  refine ⟨132972630150958316009798003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88648420100638877339865335 132972630150958316009798003)
  ·
    refine ⟨199458945226437474014697005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132972630150958316009798003 199458945226437474014697005)
    ·
      refine ⟨74797104459914052755511377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199458945226437474014697005 74797104459914052755511377)
      ·
        refine ⟨56097828344935539566633533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74797104459914052755511377 56097828344935539566633533)
        ·
          refine ⟨21036685629350827337487575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56097828344935539566633533 21036685629350827337487575)
          ·
            refine ⟨31555028444026241006231363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21036685629350827337487575 31555028444026241006231363)
            ·
              refine ⟨47332542666039361509347045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31555028444026241006231363 47332542666039361509347045)
              ·
                refine ⟨8874851749882380283002571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47332542666039361509347045 8874851749882380283002571)
                ·
                  refine ⟨13312277624823570424503857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8874851749882380283002571 13312277624823570424503857)
                  ·
                    refine ⟨9984208218617677818377893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13312277624823570424503857 9984208218617677818377893)
                    ·
                      refine ⟨1872039040990814590945855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9984208218617677818377893 1872039040990814590945855)
                      ·
                        rfl

theorem cell23_3645783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_3645783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645783 prefixEnd_3645783 := by exact prefixLift 3645783
  have htrace : WordTrace (prefixWord ++ tailWord_3645783) baseStart_3645783 baseEnd_3645783 := by
    simpa [prefixWord, tailWord_3645783, baseEnd_3645783] using wordTrace_append hprefix tailTrace_3645783
  have hstable : (prefixWord ++ tailWord_3645783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645783).length < 2 ^ (prefixWord ++ tailWord_3645783).sum := by decide
  have hdescent : baseEnd_3645783 < baseStart_3645783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645797 : List Nat := [1, 3, 1, 3, 1, 5, 1, 2, 2, 4]
def baseStart_3645797 : Nat := 118140960795 + 3645797 * 2 ^ 59
def prefixEnd_3645797 : Nat := 4983230072969 + 3 ^ 40 * 3645797 * 2
def baseEnd_3645797 : Nat := 624015409906659178723597

theorem tailTrace_3645797 : CollatzResearch.WordTrace tailWord_3645797 prefixEnd_3645797 624015409906659178723597 := by
  unfold tailWord_3645797
  simp only [CollatzResearch.WordTrace]
  refine ⟨132973140772907596400807645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88648760515271730933871763 132973140772907596400807645)
  ·
    refine ⟨49864927789840348650302867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132973140772907596400807645 49864927789840348650302867)
    ·
      refine ⟨74797391684760522975454301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49864927789840348650302867 74797391684760522975454301)
      ·
        refine ⟨28049021881785196115795363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74797391684760522975454301 28049021881785196115795363)
        ·
          refine ⟨42073532822677794173693045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28049021881785196115795363 42073532822677794173693045)
          ·
            refine ⟨3944393702126043203783723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42073532822677794173693045 3944393702126043203783723)
            ·
              refine ⟨5916590553189064805675585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944393702126043203783723 5916590553189064805675585)
              ·
                refine ⟨4437442914891798604256689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5916590553189064805675585 4437442914891798604256689)
                ·
                  refine ⟨3328082186168848953192517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4437442914891798604256689 3328082186168848953192517)
                  ·
                    refine ⟨624015409906659178723597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3328082186168848953192517 624015409906659178723597)
                    ·
                      rfl

theorem cell23_3645797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_3645797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645797 prefixEnd_3645797 := by exact prefixLift 3645797
  have htrace : WordTrace (prefixWord ++ tailWord_3645797) baseStart_3645797 baseEnd_3645797 := by
    simpa [prefixWord, tailWord_3645797, baseEnd_3645797] using wordTrace_append hprefix tailTrace_3645797
  have hstable : (prefixWord ++ tailWord_3645797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645797).length < 2 ^ (prefixWord ++ tailWord_3645797).sum := by decide
  have hdescent : baseEnd_3645797 < baseStart_3645797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645804 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 3, 2, 2]
def baseStart_3645804 : Nat := 118140960795 + 3645804 * 2 ^ 59
def prefixEnd_3645804 : Nat := 4983230072969 + 3 ^ 40 * 3645804 * 2
def baseEnd_3645804 : Nat := 1872049824084559008783259

theorem tailTrace_3645804 : CollatzResearch.WordTrace tailWord_3645804 prefixEnd_3645804 1872049824084559008783259 := by
  unfold tailWord_3645804
  simp only [CollatzResearch.WordTrace]
  refine ⟨66486698041941118298156233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88648930722588157730874977 66486698041941118298156233)
  ·
    refine ⟨49865023531455838723617175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66486698041941118298156233 49865023531455838723617175)
    ·
      refine ⟨74797535297183758085425763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49865023531455838723617175 74797535297183758085425763)
      ·
        refine ⟨112196302945775637128138645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74797535297183758085425763 112196302945775637128138645)
        ·
          refine ⟨5259201700583232990381499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112196302945775637128138645 5259201700583232990381499)
          ·
            refine ⟨7888802550874849485572249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5259201700583232990381499 7888802550874849485572249)
            ·
              refine ⟨5916601913156137114179187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7888802550874849485572249 5916601913156137114179187)
              ·
                refine ⟨8874902869734205671268781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916601913156137114179187 8874902869734205671268781)
                ·
                  refine ⟨3328088576150327126725793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8874902869734205671268781 3328088576150327126725793)
                  ·
                    refine ⟨2496066432112745345044345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3328088576150327126725793 2496066432112745345044345)
                    ·
                      refine ⟨1872049824084559008783259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496066432112745345044345 1872049824084559008783259)
                      ·
                        rfl

theorem cell23_3645804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 2, 2].length) (baseStart_3645804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645804 prefixEnd_3645804 := by exact prefixLift 3645804
  have htrace : WordTrace (prefixWord ++ tailWord_3645804) baseStart_3645804 baseEnd_3645804 := by
    simpa [prefixWord, tailWord_3645804, baseEnd_3645804] using wordTrace_append hprefix tailTrace_3645804
  have hstable : (prefixWord ++ tailWord_3645804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645804).length < 2 ^ (prefixWord ++ tailWord_3645804).sum := by decide
  have hdescent : baseEnd_3645804 < baseStart_3645804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645814 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_3645814 : Nat := 118140960795 + 3645814 * 2 ^ 59
def prefixEnd_3645814 : Nat := 4983230072969 + 3 ^ 40 * 3645814 * 2
def baseEnd_3645814 : Nat := 624018319630367989886071

theorem tailTrace_3645814 : CollatzResearch.WordTrace tailWord_3645814 prefixEnd_3645814 624018319630367989886071 := by
  unfold tailWord_3645814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8310860050865375519011031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88649173875897338869450997 8310860050865375519011031)
  ·
    refine ⟨12466290076298063278516547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8310860050865375519011031 12466290076298063278516547)
    ·
      refine ⟨18699435114447094917774821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12466290076298063278516547 18699435114447094917774821)
      ·
        refine ⟨3506144083958830297082779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18699435114447094917774821 3506144083958830297082779)
        ·
          refine ⟨5259216125938245445624169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3506144083958830297082779 5259216125938245445624169)
          ·
            refine ⟨3944412094453684084218127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5259216125938245445624169 3944412094453684084218127)
            ·
              refine ⟨5916618141680526126327191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944412094453684084218127 5916618141680526126327191)
              ·
                refine ⟨8874927212520789189490787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5916618141680526126327191 8874927212520789189490787)
                ·
                  refine ⟨13312390818781183784236181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8874927212520789189490787 13312390818781183784236181)
                  ·
                    refine ⟨624018319630367989886071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13312390818781183784236181 624018319630367989886071)
                    ·
                      rfl

theorem cell23_3645814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_3645814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645814 prefixEnd_3645814 := by exact prefixLift 3645814
  have htrace : WordTrace (prefixWord ++ tailWord_3645814) baseStart_3645814 baseEnd_3645814 := by
    simpa [prefixWord, tailWord_3645814, baseEnd_3645814] using wordTrace_append hprefix tailTrace_3645814
  have hstable : (prefixWord ++ tailWord_3645814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645814).length < 2 ^ (prefixWord ++ tailWord_3645814).sum := by decide
  have hdescent : baseEnd_3645814 < baseStart_3645814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645827 : List Nat := [1, 1, 1, 3, 7, 1, 2, 7]
def baseStart_3645827 : Nat := 118140960795 + 3645827 * 2 ^ 59
def prefixEnd_3645827 : Nat := 4983230072969 + 3 ^ 40 * 3645827 * 2
def baseEnd_3645827 : Nat := 69335616079244904399839

theorem tailTrace_3645827 : CollatzResearch.WordTrace tailWord_3645827 prefixEnd_3645827 69335616079244904399839 := by
  unfold tailWord_3645827
  simp only [CollatzResearch.WordTrace]
  refine ⟨132974234962798911524399735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88649489975199274349599823 132974234962798911524399735)
  ·
    refine ⟨199461352444198367286599603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132974234962798911524399735 199461352444198367286599603)
    ·
      refine ⟨299192028666297550929899405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199461352444198367286599603 299192028666297550929899405)
      ·
        refine ⟨112197010749861581598712277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299192028666297550929899405 112197010749861581598712277)
        ·
          refine ⟨2629617439449880818719819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 112197010749861581598712277 2629617439449880818719819)
          ·
            refine ⟨3944426159174821228079729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629617439449880818719819 3944426159174821228079729)
            ·
              refine ⟨2958319619381115921059797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3944426159174821228079729 2958319619381115921059797)
              ·
                refine ⟨69335616079244904399839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2958319619381115921059797 69335616079244904399839)
                ·
                  rfl

theorem cell23_3645827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 7].length) (baseStart_3645827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645827 prefixEnd_3645827 := by exact prefixLift 3645827
  have htrace : WordTrace (prefixWord ++ tailWord_3645827) baseStart_3645827 baseEnd_3645827 := by
    simpa [prefixWord, tailWord_3645827, baseEnd_3645827] using wordTrace_append hprefix tailTrace_3645827
  have hstable : (prefixWord ++ tailWord_3645827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645827).length < 2 ^ (prefixWord ++ tailWord_3645827).sum := by decide
  have hdescent : baseEnd_3645827 < baseStart_3645827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645833 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 5]
def baseStart_3645833 : Nat := 118140960795 + 3645833 * 2 ^ 59
def prefixEnd_3645833 : Nat := 4983230072969 + 3 ^ 40 * 3645833 * 2
def baseEnd_3645833 : Nat := 1872064715023539395320625

theorem tailTrace_3645833 : CollatzResearch.WordTrace tailWord_3645833 prefixEnd_3645833 1872064715023539395320625 := by
  unfold tailWord_3645833
  simp only [CollatzResearch.WordTrace]
  refine ⟨132974453800777174549118153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88649635867184783032745435 132974453800777174549118153)
  ·
    refine ⟨99730840350582880911838615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132974453800777174549118153 99730840350582880911838615)
    ·
      refine ⟨149596260525874321367757923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99730840350582880911838615 149596260525874321367757923)
      ·
        refine ⟨224394390788811482051636885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149596260525874321367757923 224394390788811482051636885)
        ·
          refine ⟨10518487068225538221170479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 224394390788811482051636885 10518487068225538221170479)
          ·
            refine ⟨15777730602338307331755719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10518487068225538221170479 15777730602338307331755719)
            ·
              refine ⟨23666595903507460997633579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15777730602338307331755719 23666595903507460997633579)
              ·
                refine ⟨35499893855261191496450369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23666595903507460997633579 35499893855261191496450369)
                ·
                  refine ⟨26624920391445893622337777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35499893855261191496450369 26624920391445893622337777)
                  ·
                    refine ⟨19968690293584420216753333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26624920391445893622337777 19968690293584420216753333)
                    ·
                      refine ⟨1872064715023539395320625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19968690293584420216753333 1872064715023539395320625)
                      ·
                        rfl

theorem cell23_3645833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_3645833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645833 prefixEnd_3645833 := by exact prefixLift 3645833
  have htrace : WordTrace (prefixWord ++ tailWord_3645833) baseStart_3645833 baseEnd_3645833 := by
    simpa [prefixWord, tailWord_3645833, baseEnd_3645833] using wordTrace_append hprefix tailTrace_3645833
  have hstable : (prefixWord ++ tailWord_3645833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645833).length < 2 ^ (prefixWord ++ tailWord_3645833).sum := by decide
  have hdescent : baseEnd_3645833 < baseStart_3645833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645838 : List Nat := [4, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2]
def baseStart_3645838 : Nat := 118140960795 + 3645838 * 2 ^ 59
def prefixEnd_3645838 : Nat := 4983230072969 + 3 ^ 40 * 3645838 * 2
def baseEnd_3645838 : Nat := 1872067282426811875758103

theorem tailTrace_3645838 : CollatzResearch.WordTrace tailWord_3645838 prefixEnd_3645838 1872067282426811875758103 := by
  unfold tailWord_3645838
  simp only [CollatzResearch.WordTrace]
  refine ⟨16621829520719882550381271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88649757443839373602033445 16621829520719882550381271)
  ·
    refine ⟨24932744281079823825571907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16621829520719882550381271 24932744281079823825571907)
    ·
      refine ⟨37399116421619735738357861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24932744281079823825571907 37399116421619735738357861)
      ·
        refine ⟨7012334329053700450942099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37399116421619735738357861 7012334329053700450942099)
        ·
          refine ⟨10518501493580550676413149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7012334329053700450942099 10518501493580550676413149)
          ·
            refine ⟨3944438060092706503654931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10518501493580550676413149 3944438060092706503654931)
            ·
              refine ⟨5916657090139059755482397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944438060092706503654931 5916657090139059755482397)
              ·
                refine ⟨2218746408802147408305899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5916657090139059755482397 2218746408802147408305899)
                ·
                  refine ⟨3328119613203221112458849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218746408802147408305899 3328119613203221112458849)
                  ·
                    refine ⟨2496089709902415834344137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3328119613203221112458849 2496089709902415834344137)
                    ·
                      refine ⟨1872067282426811875758103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496089709902415834344137 1872067282426811875758103)
                      ·
                        rfl

theorem cell23_3645838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_3645838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645838 prefixEnd_3645838 := by exact prefixLift 3645838
  have htrace : WordTrace (prefixWord ++ tailWord_3645838) baseStart_3645838 baseEnd_3645838 := by
    simpa [prefixWord, tailWord_3645838, baseEnd_3645838] using wordTrace_append hprefix tailTrace_3645838
  have hstable : (prefixWord ++ tailWord_3645838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645838).length < 2 ^ (prefixWord ++ tailWord_3645838).sum := by decide
  have hdescent : baseEnd_3645838 < baseStart_3645838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645847 : List Nat := [1, 1, 3, 3, 1, 1, 4, 3, 1, 3, 2]
def baseStart_3645847 : Nat := 118140960795 + 3645847 * 2 ^ 59
def prefixEnd_3645847 : Nat := 4983230072969 + 3 ^ 40 * 3645847 * 2
def baseEnd_3645847 : Nat := 1872071903752702340545561

theorem tailTrace_3645847 : CollatzResearch.WordTrace tailWord_3645847 prefixEnd_3645847 1872071903752702340545561 := by
  unfold tailWord_3645847
  simp only [CollatzResearch.WordTrace]
  refine ⟨132974964422726454940127795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88649976281817636626751863 132974964422726454940127795)
  ·
    refine ⟨199462446634089682410191693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132974964422726454940127795 199462446634089682410191693)
    ·
      refine ⟨74798417487783630903821885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199462446634089682410191693 74798417487783630903821885)
      ·
        refine ⟨28049406557918861588933207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74798417487783630903821885 28049406557918861588933207)
        ·
          refine ⟨42074109836878292383399811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28049406557918861588933207 42074109836878292383399811)
          ·
            refine ⟨63111164755317438575099717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42074109836878292383399811 63111164755317438575099717)
            ·
              refine ⟨11833343391622019732831197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63111164755317438575099717 11833343391622019732831197)
              ·
                refine ⟨4437503771858257399811699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11833343391622019732831197 4437503771858257399811699)
                ·
                  refine ⟨6656255657787386099717549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4437503771858257399811699 6656255657787386099717549)
                  ·
                    refine ⟨2496095871670269787394081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6656255657787386099717549 2496095871670269787394081)
                    ·
                      refine ⟨1872071903752702340545561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496095871670269787394081 1872071903752702340545561)
                      ·
                        rfl

theorem cell23_3645847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_3645847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645847 prefixEnd_3645847 := by exact prefixLift 3645847
  have htrace : WordTrace (prefixWord ++ tailWord_3645847) baseStart_3645847 baseEnd_3645847 := by
    simpa [prefixWord, tailWord_3645847, baseEnd_3645847] using wordTrace_append hprefix tailTrace_3645847
  have hstable : (prefixWord ++ tailWord_3645847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645847).length < 2 ^ (prefixWord ++ tailWord_3645847).sum := by decide
  have hdescent : baseEnd_3645847 < baseStart_3645847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645854 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3645854 : Nat := 118140960795 + 3645854 * 2 ^ 59
def prefixEnd_3645854 : Nat := 4983230072969 + 3 ^ 40 * 3645854 * 2
def baseEnd_3645854 : Nat := 1872075498117283813158029

theorem tailTrace_3645854 : CollatzResearch.WordTrace tailWord_3645854 prefixEnd_3645854 1872075498117283813158029 := by
  unfold tailWord_3645854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16621902466712636891954077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88650146489134063423755077 16621902466712636891954077)
  ·
    refine ⟨6233213425017238834482779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16621902466712636891954077 6233213425017238834482779)
    ·
      refine ⟨9349820137525858251724169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6233213425017238834482779 9349820137525858251724169)
      ·
        refine ⟨7012365103144393688793127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9349820137525858251724169 7012365103144393688793127)
        ·
          refine ⟨10518547654716590533189691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7012365103144393688793127 10518547654716590533189691)
          ·
            refine ⟨15777821482074885799784537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10518547654716590533189691 15777821482074885799784537)
            ·
              refine ⟨11833366111556164349838403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15777821482074885799784537 11833366111556164349838403)
              ·
                refine ⟨17750049167334246524757605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11833366111556164349838403 17750049167334246524757605)
                ·
                  refine ⟨3328134218875171223392051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17750049167334246524757605 3328134218875171223392051)
                  ·
                    refine ⟨4992201328312756835088077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3328134218875171223392051 4992201328312756835088077)
                    ·
                      refine ⟨1872075498117283813158029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4992201328312756835088077 1872075498117283813158029)
                      ·
                        rfl

theorem cell23_3645854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3645854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645854 prefixEnd_3645854 := by exact prefixLift 3645854
  have htrace : WordTrace (prefixWord ++ tailWord_3645854) baseStart_3645854 baseEnd_3645854 := by
    simpa [prefixWord, tailWord_3645854, baseEnd_3645854] using wordTrace_append hprefix tailTrace_3645854
  have hstable : (prefixWord ++ tailWord_3645854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645854).length < 2 ^ (prefixWord ++ tailWord_3645854).sum := by decide
  have hdescent : baseEnd_3645854 < baseStart_3645854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645917 : List Nat := [1, 4, 3, 1, 1, 1, 3, 4, 5]
def baseStart_3645917 : Nat := 118140960795 + 3645917 * 2 ^ 59
def prefixEnd_3645917 : Nat := 4983230072969 + 3 ^ 40 * 3645917 * 2
def baseEnd_3645917 : Nat := 208011983044279674074471

theorem tailTrace_3645917 : CollatzResearch.WordTrace tailWord_3645917 prefixEnd_3645917 208011983044279674074471 := by
  unfold tailWord_3645917
  simp only [CollatzResearch.WordTrace]
  refine ⟨132977517532472856895176005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88651678354981904596784003 132977517532472856895176005)
  ·
    refine ⟨24933284537338660667845501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132977517532472856895176005 24933284537338660667845501)
    ·
      refine ⟨9349981701501997750442063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24933284537338660667845501 9349981701501997750442063)
      ·
        refine ⟨14024972552252996625663095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9349981701501997750442063 14024972552252996625663095)
        ·
          refine ⟨21037458828379494938494643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14024972552252996625663095 21037458828379494938494643)
          ·
            refine ⟨31556188242569242407741965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21037458828379494938494643 31556188242569242407741965)
            ·
              refine ⟨11833570590963465902903237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31556188242569242407741965 11833570590963465902903237)
              ·
                refine ⟨2218794485805649856794357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11833570590963465902903237 2218794485805649856794357)
                ·
                  refine ⟨208011983044279674074471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2218794485805649856794357 208011983044279674074471)
                  ·
                    rfl

theorem cell23_3645917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_3645917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645917 prefixEnd_3645917 := by exact prefixLift 3645917
  have htrace : WordTrace (prefixWord ++ tailWord_3645917) baseStart_3645917 baseEnd_3645917 := by
    simpa [prefixWord, tailWord_3645917, baseEnd_3645917] using wordTrace_append hprefix tailTrace_3645917
  have hstable : (prefixWord ++ tailWord_3645917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645917).length < 2 ^ (prefixWord ++ tailWord_3645917).sum := by decide
  have hdescent : baseEnd_3645917 < baseStart_3645917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645920 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 1, 7, 2]
def baseStart_3645920 : Nat := 118140960795 + 3645920 * 2 ^ 59
def prefixEnd_3645920 : Nat := 4983230072969 + 3 ^ 40 * 3645920 * 2
def baseEnd_3645920 : Nat := 1872109387840480554932725

theorem tailTrace_3645920 : CollatzResearch.WordTrace tailWord_3645920 prefixEnd_3645920 1872109387840480554932725 := by
  unfold tailWord_3645920
  simp only [CollatzResearch.WordTrace]
  refine ⟨66488813475730994203767607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88651751300974658938356809 66488813475730994203767607)
  ·
    refine ⟨99733220213596491305651411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66488813475730994203767607 99733220213596491305651411)
    ·
      refine ⟨149599830320394736958477117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99733220213596491305651411 149599830320394736958477117)
      ·
        refine ⟨56099936370148026359428919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149599830320394736958477117 56099936370148026359428919)
        ·
          refine ⟨84149904555222039539143379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56099936370148026359428919 84149904555222039539143379)
          ·
            refine ⟨126224856832833059308715069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84149904555222039539143379 126224856832833059308715069)
            ·
              refine ⟨47334321312312397240768151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126224856832833059308715069 47334321312312397240768151)
              ·
                refine ⟨71001481968468595861152227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47334321312312397240768151 71001481968468595861152227)
                ·
                  refine ⟨106502222952702893791728341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71001481968468595861152227 106502222952702893791728341)
                  ·
                    refine ⟨2496145850453974073243633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 106502222952702893791728341 2496145850453974073243633)
                    ·
                      refine ⟨1872109387840480554932725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496145850453974073243633 1872109387840480554932725)
                      ·
                        rfl

theorem cell23_3645920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_3645920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645920 prefixEnd_3645920 := by exact prefixLift 3645920
  have htrace : WordTrace (prefixWord ++ tailWord_3645920) baseStart_3645920 baseEnd_3645920 := by
    simpa [prefixWord, tailWord_3645920, baseEnd_3645920] using wordTrace_append hprefix tailTrace_3645920
  have hstable : (prefixWord ++ tailWord_3645920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645920).length < 2 ^ (prefixWord ++ tailWord_3645920).sum := by decide
  have hdescent : baseEnd_3645920 < baseStart_3645920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3645960 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 7, 4]
def baseStart_3645960 : Nat := 118140960795 + 3645960 * 2 ^ 59
def prefixEnd_3645960 : Nat := 4983230072969 + 3 ^ 40 * 3645960 * 2
def baseEnd_3645960 : Nat := 624043309022220132810847

theorem tailTrace_3645960 : CollatzResearch.WordTrace tailWord_3645960 prefixEnd_3645960 624043309022220132810847 := by
  unfold tailWord_3645960
  simp only [CollatzResearch.WordTrace]
  refine ⟨66489542935658537619495667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88652723914211383492660889 66489542935658537619495667)
  ·
    refine ⟨99734314403487806429243501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66489542935658537619495667 99734314403487806429243501)
    ·
      refine ⟨37400367901307927410966313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99734314403487806429243501 37400367901307927410966313)
      ·
        refine ⟨28050275925980945558224735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37400367901307927410966313 28050275925980945558224735)
        ·
          refine ⟨42075413888971418337337103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28050275925980945558224735 42075413888971418337337103)
          ·
            refine ⟨63113120833457127506005655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42075413888971418337337103 63113120833457127506005655)
            ·
              refine ⟨94669681250185691259008483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63113120833457127506005655 94669681250185691259008483)
              ·
                refine ⟨142004521875278536888512725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94669681250185691259008483 142004521875278536888512725)
                ·
                  refine ⟨3328230981451840708324517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 142004521875278536888512725 3328230981451840708324517)
                  ·
                    refine ⟨624043309022220132810847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3328230981451840708324517 624043309022220132810847)
                    ·
                      rfl

theorem cell23_3645960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_3645960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3645960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3645960 prefixEnd_3645960 := by exact prefixLift 3645960
  have htrace : WordTrace (prefixWord ++ tailWord_3645960) baseStart_3645960 baseEnd_3645960 := by
    simpa [prefixWord, tailWord_3645960, baseEnd_3645960] using wordTrace_append hprefix tailTrace_3645960
  have hstable : (prefixWord ++ tailWord_3645960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3645960).length < 2 ^ (prefixWord ++ tailWord_3645960).sum := by decide
  have hdescent : baseEnd_3645960 < baseStart_3645960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3645960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646027 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 4, 3, 2]
def baseStart_3646027 : Nat := 118140960795 + 3646027 * 2 ^ 59
def prefixEnd_3646027 : Nat := 4983230072969 + 3 ^ 40 * 3646027 * 2
def baseEnd_3646027 : Nat := 1872164330270511636294733

theorem tailTrace_3646027 : CollatzResearch.WordTrace tailWord_3646027 prefixEnd_3646027 1872164330270511636294733 := by
  unfold tailWord_3646027
  simp only [CollatzResearch.WordTrace]
  refine ⟨132981529562074345681680335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88654353041382897121120223 132981529562074345681680335)
  ·
    refine ⟨199472294343111518522520503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132981529562074345681680335 199472294343111518522520503)
    ·
      refine ⟨299208441514667277783780755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199472294343111518522520503 299208441514667277783780755)
      ·
        refine ⟨448812662272000916675671133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299208441514667277783780755 448812662272000916675671133)
        ·
          refine ⟨168304748352000343753376675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448812662272000916675671133 168304748352000343753376675)
          ·
            refine ⟨252457122528000515630065013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168304748352000343753376675 252457122528000515630065013)
            ·
              refine ⟨23667855237000048340318595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252457122528000515630065013 23667855237000048340318595)
              ·
                refine ⟨35501782855500072510477893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23667855237000048340318595 35501782855500072510477893)
                ·
                  refine ⟨6656584285406263595714605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35501782855500072510477893 6656584285406263595714605)
                  ·
                    refine ⟨2496219107027348848392977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6656584285406263595714605 2496219107027348848392977)
                    ·
                      refine ⟨1872164330270511636294733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496219107027348848392977 1872164330270511636294733)
                      ·
                        rfl

theorem cell23_3646027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 4, 3, 2].length) (baseStart_3646027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646027 prefixEnd_3646027 := by exact prefixLift 3646027
  have htrace : WordTrace (prefixWord ++ tailWord_3646027) baseStart_3646027 baseEnd_3646027 := by
    simpa [prefixWord, tailWord_3646027, baseEnd_3646027] using wordTrace_append hprefix tailTrace_3646027
  have hstable : (prefixWord ++ tailWord_3646027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646027).length < 2 ^ (prefixWord ++ tailWord_3646027).sum := by decide
  have hdescent : baseEnd_3646027 < baseStart_3646027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646060 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 5]
def baseStart_3646060 : Nat := 118140960795 + 3646060 * 2 ^ 59
def prefixEnd_3646060 : Nat := 4983230072969 + 3 ^ 40 * 3646060 * 2
def baseEnd_3646060 : Nat := 1872181275132110007182081

theorem tailTrace_3646060 : CollatzResearch.WordTrace tailWord_3646060 prefixEnd_3646060 1872181275132110007182081 := by
  unfold tailWord_3646060
  simp only [CollatzResearch.WordTrace]
  refine ⟨66491366585477396158815817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88655155447303194878421089 66491366585477396158815817)
  ·
    refine ⟨49868524939108047119111863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66491366585477396158815817 49868524939108047119111863)
    ·
      refine ⟨74802787408662070678667795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49868524939108047119111863 74802787408662070678667795)
      ·
        refine ⟨112204181112993106018001693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74802787408662070678667795 112204181112993106018001693)
        ·
          refine ⟨42076567917372414756750635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112204181112993106018001693 42076567917372414756750635)
          ·
            refine ⟨63114851876058622135125953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42076567917372414756750635 63114851876058622135125953)
            ·
              refine ⟨47336138907043966601344465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63114851876058622135125953 47336138907043966601344465)
              ·
                refine ⟨35502104180282974951008349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47336138907043966601344465 35502104180282974951008349)
                ·
                  refine ⟨13313289067606115606628131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35502104180282974951008349 13313289067606115606628131)
                  ·
                    refine ⟨19969933601409173409942197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13313289067606115606628131 19969933601409173409942197)
                    ·
                      refine ⟨1872181275132110007182081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19969933601409173409942197 1872181275132110007182081)
                      ·
                        rfl

theorem cell23_3646060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_3646060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646060 prefixEnd_3646060 := by exact prefixLift 3646060
  have htrace : WordTrace (prefixWord ++ tailWord_3646060) baseStart_3646060 baseEnd_3646060 := by
    simpa [prefixWord, tailWord_3646060, baseEnd_3646060] using wordTrace_append hprefix tailTrace_3646060
  have hstable : (prefixWord ++ tailWord_3646060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646060).length < 2 ^ (prefixWord ++ tailWord_3646060).sum := by decide
  have hdescent : baseEnd_3646060 < baseStart_3646060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646061 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_3646061 : Nat := 118140960795 + 3646061 * 2 ^ 59
def prefixEnd_3646061 : Nat := 4983230072969 + 3 ^ 40 * 3646061 * 2
def baseEnd_3646061 : Nat := 1872181788612764503269577

theorem tailTrace_3646061 : CollatzResearch.WordTrace tailWord_3646061 prefixEnd_3646061 1872181788612764503269577 := by
  unfold tailWord_3646061
  simp only [CollatzResearch.WordTrace]
  refine ⟨132982769643951169488418037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88655179762634112992278691 132982769643951169488418037)
  ·
    refine ⟨12467134654120422139539191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132982769643951169488418037 12467134654120422139539191)
    ·
      refine ⟨18700701981180633209308787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12467134654120422139539191 18700701981180633209308787)
      ·
        refine ⟨28051052971770949813963181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18700701981180633209308787 28051052971770949813963181)
        ·
          refine ⟨10519144864414106180236193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28051052971770949813963181 10519144864414106180236193)
          ·
            refine ⟨7889358648310579635177145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10519144864414106180236193 7889358648310579635177145)
            ·
              refine ⟨5917018986232934726382859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7889358648310579635177145 5917018986232934726382859)
              ·
                refine ⟨8875528479349402089574289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917018986232934726382859 8875528479349402089574289)
                ·
                  refine ⟨6656646359512051567180717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8875528479349402089574289 6656646359512051567180717)
                  ·
                    refine ⟨2496242384817019337692769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6656646359512051567180717 2496242384817019337692769)
                    ·
                      refine ⟨1872181788612764503269577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496242384817019337692769 1872181788612764503269577)
                      ·
                        rfl

theorem cell23_3646061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_3646061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646061 prefixEnd_3646061 := by exact prefixLift 3646061
  have htrace : WordTrace (prefixWord ++ tailWord_3646061) baseStart_3646061 baseEnd_3646061 := by
    simpa [prefixWord, tailWord_3646061, baseEnd_3646061] using wordTrace_append hprefix tailTrace_3646061
  have hstable : (prefixWord ++ tailWord_3646061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646061).length < 2 ^ (prefixWord ++ tailWord_3646061).sum := by decide
  have hdescent : baseEnd_3646061 < baseStart_3646061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646084 : List Nat := [2, 3, 2, 1, 3, 1, 1, 4, 2, 4]
def baseStart_3646084 : Nat := 118140960795 + 3646084 * 2 ^ 59
def prefixEnd_3646084 : Nat := 4983230072969 + 3 ^ 40 * 3646084 * 2
def baseEnd_3646084 : Nat := 624064532889272637760657

theorem tailTrace_3646084 : CollatzResearch.WordTrace tailWord_3646084 prefixEnd_3646084 624064532889272637760657 := by
  unfold tailWord_3646084
  simp only [CollatzResearch.WordTrace]
  refine ⟨66491804261433922208252653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88655739015245229611003537 66491804261433922208252653)
  ·
    refine ⟨24934426598037720828094745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66491804261433922208252653 24934426598037720828094745)
    ·
      refine ⟨18700819948528290621071059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24934426598037720828094745 18700819948528290621071059)
      ·
        refine ⟨28051229922792435931606589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18700819948528290621071059 28051229922792435931606589)
        ·
          refine ⟨10519211221047163474352471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28051229922792435931606589 10519211221047163474352471)
          ·
            refine ⟨15778816831570745211528707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10519211221047163474352471 15778816831570745211528707)
            ·
              refine ⟨23668225247356117817293061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15778816831570745211528707 23668225247356117817293061)
              ·
                refine ⟨4437792233879272090742449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23668225247356117817293061 4437792233879272090742449)
                ·
                  refine ⟨3328344175409454068056837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4437792233879272090742449 3328344175409454068056837)
                  ·
                    refine ⟨624064532889272637760657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3328344175409454068056837 624064532889272637760657)
                    ·
                      rfl

theorem cell23_3646084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_3646084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646084 prefixEnd_3646084 := by exact prefixLift 3646084
  have htrace : WordTrace (prefixWord ++ tailWord_3646084) baseStart_3646084 baseEnd_3646084 := by
    simpa [prefixWord, tailWord_3646084, baseEnd_3646084] using wordTrace_append hprefix tailTrace_3646084
  have hstable : (prefixWord ++ tailWord_3646084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646084).length < 2 ^ (prefixWord ++ tailWord_3646084).sum := by decide
  have hdescent : baseEnd_3646084 < baseStart_3646084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646125 : List Nat := [1, 5, 2, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_3646125 : Nat := 118140960795 + 3646125 * 2 ^ 59
def prefixEnd_3646125 : Nat := 4983230072969 + 3 ^ 40 * 3646125 * 2
def baseEnd_3646125 : Nat := 1872214651374652252869283

theorem tailTrace_3646125 : CollatzResearch.WordTrace tailWord_3646125 prefixEnd_3646125 1872214651374652252869283 := by
  unfold tailWord_3646125
  simp only [CollatzResearch.WordTrace]
  refine ⟨132985103915719308418747829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88656735943812872279165219 132985103915719308418747829)
  ·
    refine ⟨12467353492098685164257609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132985103915719308418747829 12467353492098685164257609)
    ·
      refine ⟨9350515119074013873193207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12467353492098685164257609 9350515119074013873193207)
      ·
        refine ⟨14025772678611020809789811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9350515119074013873193207 14025772678611020809789811)
        ·
          refine ⟨21038659017916531214684717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14025772678611020809789811 21038659017916531214684717)
          ·
            refine ⟨7889497131718699205506769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21038659017916531214684717 7889497131718699205506769)
            ·
              refine ⟨5917122848789024404130077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7889497131718699205506769 5917122848789024404130077)
              ·
                refine ⟨2218921068295884151548779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5917122848789024404130077 2218921068295884151548779)
                ·
                  refine ⟨3328381602443826227323169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2218921068295884151548779 3328381602443826227323169)
                  ·
                    refine ⟨2496286201832869670492377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3328381602443826227323169 2496286201832869670492377)
                    ·
                      refine ⟨1872214651374652252869283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496286201832869670492377 1872214651374652252869283)
                      ·
                        rfl

theorem cell23_3646125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_3646125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646125 prefixEnd_3646125 := by exact prefixLift 3646125
  have htrace : WordTrace (prefixWord ++ tailWord_3646125) baseStart_3646125 baseEnd_3646125 := by
    simpa [prefixWord, tailWord_3646125, baseEnd_3646125] using wordTrace_append hprefix tailTrace_3646125
  have hstable : (prefixWord ++ tailWord_3646125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646125).length < 2 ^ (prefixWord ++ tailWord_3646125).sum := by decide
  have hdescent : baseEnd_3646125 < baseStart_3646125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646141 : List Nat := [1, 4, 1, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_3646141 : Nat := 118140960795 + 3646141 * 2 ^ 59
def prefixEnd_3646141 : Nat := 4983230072969 + 3 ^ 40 * 3646141 * 2
def baseEnd_3646141 : Nat := 1872222867065124190269209

theorem tailTrace_3646141 : CollatzResearch.WordTrace tailWord_3646141 prefixEnd_3646141 1872222867065124190269209 := by
  unfold tailWord_3646141
  simp only [CollatzResearch.WordTrace]
  refine ⟨132985687483661343151330277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88657124989107562100886851 132985687483661343151330277)
  ·
    refine ⟨24934816403186501840874427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132985687483661343151330277 24934816403186501840874427)
    ·
      refine ⟨37402224604779752761311641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24934816403186501840874427 37402224604779752761311641)
      ·
        refine ⟨28051668453584814570983731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37402224604779752761311641 28051668453584814570983731)
        ·
          refine ⟨42077502680377221856475597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28051668453584814570983731 42077502680377221856475597)
          ·
            refine ⟨15779063505141458196178349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42077502680377221856475597 15779063505141458196178349)
            ·
              refine ⟨5917148814428046823566881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15779063505141458196178349 5917148814428046823566881)
              ·
                refine ⟨4437861610821035117675161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5917148814428046823566881 4437861610821035117675161)
                ·
                  refine ⟨3328396208115776338256371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4437861610821035117675161 3328396208115776338256371)
                  ·
                    refine ⟨4992594312173664507384557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3328396208115776338256371 4992594312173664507384557)
                    ·
                      refine ⟨1872222867065124190269209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4992594312173664507384557 1872222867065124190269209)
                      ·
                        rfl

theorem cell23_3646141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_3646141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646141 prefixEnd_3646141 := by exact prefixLift 3646141
  have htrace : WordTrace (prefixWord ++ tailWord_3646141) baseStart_3646141 baseEnd_3646141 := by
    simpa [prefixWord, tailWord_3646141, baseEnd_3646141] using wordTrace_append hprefix tailTrace_3646141
  have hstable : (prefixWord ++ tailWord_3646141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646141).length < 2 ^ (prefixWord ++ tailWord_3646141).sum := by decide
  have hdescent : baseEnd_3646141 < baseStart_3646141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646147 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 1, 10, 2]
def baseStart_3646147 : Nat := 118140960795 + 3646147 * 2 ^ 59
def prefixEnd_3646147 : Nat := 4983230072969 + 3 ^ 40 * 3646147 * 2
def baseEnd_3646147 : Nat := 1872225947949051166794181

theorem tailTrace_3646147 : CollatzResearch.WordTrace tailWord_3646147 prefixEnd_3646147 1872225947949051166794181 := by
  unfold tailWord_3646147
  simp only [CollatzResearch.WordTrace]
  refine ⟨132985906321639606176048695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88657270881093070784032463 132985906321639606176048695)
  ·
    refine ⟨199478859482459409264073043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132985906321639606176048695 199478859482459409264073043)
    ·
      refine ⟨299218289223689113896109565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199478859482459409264073043 299218289223689113896109565)
      ·
        refine ⟨112206858458883417711041087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299218289223689113896109565 112206858458883417711041087)
        ·
          refine ⟨168310287688325126566561631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112206858458883417711041087 168310287688325126566561631)
          ·
            refine ⟨252465431532487689849842447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168310287688325126566561631 252465431532487689849842447)
            ·
              refine ⟨378698147298731534774763671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252465431532487689849842447 378698147298731534774763671)
              ·
                refine ⟨568047220948097302162145507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378698147298731534774763671 568047220948097302162145507)
                ·
                  refine ⟨852070831422145953243218261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 568047220948097302162145507 852070831422145953243218261)
                  ·
                    refine ⟨2496301263932068222392241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 852070831422145953243218261 2496301263932068222392241)
                    ·
                      refine ⟨1872225947949051166794181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496301263932068222392241 1872225947949051166794181)
                      ·
                        rfl

theorem cell23_3646147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 10, 2].length) (baseStart_3646147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646147 prefixEnd_3646147 := by exact prefixLift 3646147
  have htrace : WordTrace (prefixWord ++ tailWord_3646147) baseStart_3646147 baseEnd_3646147 := by
    simpa [prefixWord, tailWord_3646147, baseEnd_3646147] using wordTrace_append hprefix tailTrace_3646147
  have hstable : (prefixWord ++ tailWord_3646147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646147).length < 2 ^ (prefixWord ++ tailWord_3646147).sum := by decide
  have hdescent : baseEnd_3646147 < baseStart_3646147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646158 : List Nat := [4, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3]
def baseStart_3646158 : Nat := 118140960795 + 3646158 * 2 ^ 59
def prefixEnd_3646158 : Nat := 4983230072969 + 3 ^ 40 * 3646158 * 2
def baseEnd_3646158 : Nat := 1872231596236250623756631

theorem tailTrace_3646158 : CollatzResearch.WordTrace tailWord_3646158 prefixEnd_3646158 1872231596236250623756631 := by
  unfold tailWord_3646158
  simp only [CollatzResearch.WordTrace]
  refine ⟨16623288440574969381837391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88657538349733170036466085 16623288440574969381837391)
  ·
    refine ⟨24934932660862454072756087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16623288440574969381837391 24934932660862454072756087)
    ·
      refine ⟨37402398991293681109134131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24934932660862454072756087 37402398991293681109134131)
      ·
        refine ⟨56103598486940521663701197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37402398991293681109134131 56103598486940521663701197)
        ·
          refine ⟨21038849432602695623887949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56103598486940521663701197 21038849432602695623887949)
          ·
            refine ⟨7889568537226010858957981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21038849432602695623887949 7889568537226010858957981)
            ·
              refine ⟨2958588201459754072109243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7889568537226010858957981 2958588201459754072109243)
              ·
                refine ⟨4437882302189631108163865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958588201459754072109243 4437882302189631108163865)
                ·
                  refine ⟨3328411726642223331122899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4437882302189631108163865 3328411726642223331122899)
                  ·
                    refine ⟨4992617589963334996684349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3328411726642223331122899 4992617589963334996684349)
                    ·
                      refine ⟨1872231596236250623756631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4992617589963334996684349 1872231596236250623756631)
                      ·
                        rfl

theorem cell23_3646158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_3646158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646158 prefixEnd_3646158 := by exact prefixLift 3646158
  have htrace : WordTrace (prefixWord ++ tailWord_3646158) baseStart_3646158 baseEnd_3646158 := by
    simpa [prefixWord, tailWord_3646158, baseEnd_3646158] using wordTrace_append hprefix tailTrace_3646158
  have hstable : (prefixWord ++ tailWord_3646158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646158).length < 2 ^ (prefixWord ++ tailWord_3646158).sum := by decide
  have hdescent : baseEnd_3646158 < baseStart_3646158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646181 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 4, 2, 2]
def baseStart_3646181 : Nat := 118140960795 + 3646181 * 2 ^ 59
def prefixEnd_3646181 : Nat := 4983230072969 + 3 ^ 40 * 3646181 * 2
def baseEnd_3646181 : Nat := 1872243406291304033769025

theorem tailTrace_3646181 : CollatzResearch.WordTrace tailWord_3646181 prefixEnd_3646181 1872243406291304033769025 := by
  unfold tailWord_3646181
  simp only [CollatzResearch.WordTrace]
  refine ⟨132987146403516429982786397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88658097602344286655190931 132987146403516429982786397)
  ·
    refine ⟨49870179901318661243544899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132987146403516429982786397 49870179901318661243544899)
    ·
      refine ⟨74805269851977991865317349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49870179901318661243544899 74805269851977991865317349)
      ·
        refine ⟨14025988097245873474747003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74805269851977991865317349 14025988097245873474747003)
        ·
          refine ⟨21038982145868810212120505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14025988097245873474747003 21038982145868810212120505)
          ·
            refine ⟨15779236609401607659090379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21038982145868810212120505 15779236609401607659090379)
            ·
              refine ⟨23668854914102411488635569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15779236609401607659090379 23668854914102411488635569)
              ·
                refine ⟨17751641185576808616476677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23668854914102411488635569 17751641185576808616476677)
                ·
                  refine ⟨3328432722295651615589377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17751641185576808616476677 3328432722295651615589377)
                  ·
                    refine ⟨2496324541721738711692033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3328432722295651615589377 2496324541721738711692033)
                    ·
                      refine ⟨1872243406291304033769025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496324541721738711692033 1872243406291304033769025)
                      ·
                        rfl

theorem cell23_3646181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_3646181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646181 prefixEnd_3646181 := by exact prefixLift 3646181
  have htrace : WordTrace (prefixWord ++ tailWord_3646181) baseStart_3646181 baseEnd_3646181 := by
    simpa [prefixWord, tailWord_3646181, baseEnd_3646181] using wordTrace_append hprefix tailTrace_3646181
  have hstable : (prefixWord ++ tailWord_3646181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646181).length < 2 ^ (prefixWord ++ tailWord_3646181).sum := by decide
  have hdescent : baseEnd_3646181 < baseStart_3646181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646184 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_3646184 : Nat := 118140960795 + 3646184 * 2 ^ 59
def prefixEnd_3646184 : Nat := 4983230072969 + 3 ^ 40 * 3646184 * 2
def baseEnd_3646184 : Nat := 1872244946733267522031511

theorem tailTrace_3646184 : CollatzResearch.WordTrace tailWord_3646184 prefixEnd_3646184 1872244946733267522031511 := by
  unfold tailWord_3646184
  simp only [CollatzResearch.WordTrace]
  refine ⟨66493627911252780747572803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88658170548337040996763737 66493627911252780747572803)
  ·
    refine ⟨99740441866879171121359205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66493627911252780747572803 99740441866879171121359205)
    ·
      refine ⟨18701332850039844585254851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99740441866879171121359205 18701332850039844585254851)
      ·
        refine ⟨28051999275059766877882277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18701332850039844585254851 28051999275059766877882277)
        ·
          refine ⟨5259749864073706289602927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28051999275059766877882277 5259749864073706289602927)
          ·
            refine ⟨7889624796110559434404391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5259749864073706289602927 7889624796110559434404391)
            ·
              refine ⟨11834437194165839151606587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7889624796110559434404391 11834437194165839151606587)
              ·
                refine ⟨17751655791248758727409881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11834437194165839151606587 17751655791248758727409881)
                ·
                  refine ⟨13313741843436569045557411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17751655791248758727409881 13313741843436569045557411)
                  ·
                    refine ⟨19970612765154853568336117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13313741843436569045557411 19970612765154853568336117)
                    ·
                      refine ⟨1872244946733267522031511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19970612765154853568336117 1872244946733267522031511)
                      ·
                        rfl

theorem cell23_3646184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_3646184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646184 prefixEnd_3646184 := by exact prefixLift 3646184
  have htrace : WordTrace (prefixWord ++ tailWord_3646184) baseStart_3646184 baseEnd_3646184 := by
    simpa [prefixWord, tailWord_3646184, baseEnd_3646184] using wordTrace_append hprefix tailTrace_3646184
  have hstable : (prefixWord ++ tailWord_3646184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646184).length < 2 ^ (prefixWord ++ tailWord_3646184).sum := by decide
  have hdescent : baseEnd_3646184 < baseStart_3646184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646198 : List Nat := [5, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_3646198 : Nat := 118140960795 + 3646198 * 2 ^ 59
def prefixEnd_3646198 : Nat := 4983230072969 + 3 ^ 40 * 3646198 * 2
def baseEnd_3646198 : Nat := 1872252135462430467256447

theorem tailTrace_3646198 : CollatzResearch.WordTrace tailWord_3646198 prefixEnd_3646198 1872252135462430467256447 := by
  unfold tailWord_3646198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8311735402778427617884703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88658510962969894590770165 8311735402778427617884703)
  ·
    refine ⟨12467603104167641426827055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8311735402778427617884703 12467603104167641426827055)
    ·
      refine ⟨18701404656251462140240583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12467603104167641426827055 18701404656251462140240583)
      ·
        refine ⟨28052106984377193210360875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18701404656251462140240583 28052106984377193210360875)
        ·
          refine ⟨42078160476565789815541313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28052106984377193210360875 42078160476565789815541313)
          ·
            refine ⟨31558620357424342361655985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42078160476565789815541313 31558620357424342361655985)
            ·
              refine ⟨23668965268068256771241989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31558620357424342361655985 23668965268068256771241989)
              ·
                refine ⟨4437930987762798144607873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23668965268068256771241989 4437930987762798144607873)
                ·
                  refine ⟨3328448240822098608455905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4437930987762798144607873 3328448240822098608455905)
                  ·
                    refine ⟨2496336180616573956341929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3328448240822098608455905 2496336180616573956341929)
                    ·
                      refine ⟨1872252135462430467256447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496336180616573956341929 1872252135462430467256447)
                      ·
                        rfl

theorem cell23_3646198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_3646198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646198 prefixEnd_3646198 := by exact prefixLift 3646198
  have htrace : WordTrace (prefixWord ++ tailWord_3646198) baseStart_3646198 baseEnd_3646198 := by
    simpa [prefixWord, tailWord_3646198, baseEnd_3646198] using wordTrace_append hprefix tailTrace_3646198
  have hstable : (prefixWord ++ tailWord_3646198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646198).length < 2 ^ (prefixWord ++ tailWord_3646198).sum := by decide
  have hdescent : baseEnd_3646198 < baseStart_3646198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646204 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 7]
def baseStart_3646204 : Nat := 118140960795 + 3646204 * 2 ^ 59
def prefixEnd_3646204 : Nat := 4983230072969 + 3 ^ 40 * 3646204 * 2
def baseEnd_3646204 : Nat := 208028357371817493753491

theorem tailTrace_3646204 : CollatzResearch.WordTrace tailWord_3646204 prefixEnd_3646204 208028357371817493753491 := by
  unfold tailWord_3646204
  simp only [CollatzResearch.WordTrace]
  refine ⟨66493992641216552455436833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88658656854955403273915777 66493992641216552455436833)
  ·
    refine ⟨49870494480912414341577625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66493992641216552455436833 49870494480912414341577625)
    ·
      refine ⟨37402870860684310756183219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49870494480912414341577625 37402870860684310756183219)
      ·
        refine ⟨56104306291026466134274829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37402870860684310756183219 56104306291026466134274829)
        ·
          refine ⟨21039114859134924800353061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56104306291026466134274829 21039114859134924800353061)
          ·
            refine ⟨3944834036087798400066199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21039114859134924800353061 3944834036087798400066199)
            ·
              refine ⟨5917251054131697600099299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944834036087798400066199 5917251054131697600099299)
              ·
                refine ⟨8875876581197546400148949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917251054131697600099299 8875876581197546400148949)
                ·
                  refine ⟨208028357371817493753491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8875876581197546400148949 208028357371817493753491)
                  ·
                    rfl

theorem cell23_3646204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 7].length) (baseStart_3646204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646204 prefixEnd_3646204 := by exact prefixLift 3646204
  have htrace : WordTrace (prefixWord ++ tailWord_3646204) baseStart_3646204 baseEnd_3646204 := by
    simpa [prefixWord, tailWord_3646204, baseEnd_3646204] using wordTrace_append hprefix tailTrace_3646204
  have hstable : (prefixWord ++ tailWord_3646204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646204).length < 2 ^ (prefixWord ++ tailWord_3646204).sum := by decide
  have hdescent : baseEnd_3646204 < baseStart_3646204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646215 : List Nat := [1, 1, 4, 4, 1, 1, 4, 1, 2, 2, 2]
def baseStart_3646215 : Nat := 118140960795 + 3646215 * 2 ^ 59
def prefixEnd_3646215 : Nat := 4983230072969 + 3 ^ 40 * 3646215 * 2
def baseEnd_3646215 : Nat := 1872260864633556900743869

theorem tailTrace_3646215 : CollatzResearch.WordTrace tailWord_3646215 prefixEnd_3646215 1872260864633556900743869 := by
  unfold tailWord_3646215
  simp only [CollatzResearch.WordTrace]
  refine ⟨132988386485393253789524099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88658924323595502526349399 132988386485393253789524099)
  ·
    refine ⟨199482579728089880684286149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132988386485393253789524099 199482579728089880684286149)
    ·
      refine ⟨37402983699016852628303653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199482579728089880684286149 37402983699016852628303653)
      ·
        refine ⟨7013059443565659867806935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37402983699016852628303653 7013059443565659867806935)
        ·
          refine ⟨10519589165348489801710403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7013059443565659867806935 10519589165348489801710403)
          ·
            refine ⟨15779383748022734702565605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10519589165348489801710403 15779383748022734702565605)
            ·
              refine ⟨2958634452754262756731051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15779383748022734702565605 2958634452754262756731051)
              ·
                refine ⟨4437951679131394135096577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958634452754262756731051 4437951679131394135096577)
                ·
                  refine ⟨3328463759348545601322433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4437951679131394135096577 3328463759348545601322433)
                  ·
                    refine ⟨2496347819511409200991825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3328463759348545601322433 2496347819511409200991825)
                    ·
                      refine ⟨1872260864633556900743869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496347819511409200991825 1872260864633556900743869)
                      ·
                        rfl

theorem cell23_3646215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_3646215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646215 prefixEnd_3646215 := by exact prefixLift 3646215
  have htrace : WordTrace (prefixWord ++ tailWord_3646215) baseStart_3646215 baseEnd_3646215 := by
    simpa [prefixWord, tailWord_3646215, baseEnd_3646215] using wordTrace_append hprefix tailTrace_3646215
  have hstable : (prefixWord ++ tailWord_3646215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646215).length < 2 ^ (prefixWord ++ tailWord_3646215).sum := by decide
  have hdescent : baseEnd_3646215 < baseStart_3646215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646234 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 2, 5]
def baseStart_3646234 : Nat := 118140960795 + 3646234 * 2 ^ 59
def prefixEnd_3646234 : Nat := 4983230072969 + 3 ^ 40 * 3646234 * 2
def baseEnd_3646234 : Nat := 624090206921997442135427

theorem tailTrace_3646234 : CollatzResearch.WordTrace tailWord_3646234 prefixEnd_3646234 624090206921997442135427 := by
  unfold tailWord_3646234
  simp only [CollatzResearch.WordTrace]
  refine ⟨33247269868081105008616439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88659386314882946689643837 33247269868081105008616439)
  ·
    refine ⟨49870904802121657512924659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33247269868081105008616439 49870904802121657512924659)
    ·
      refine ⟨74806357203182486269386989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49870904802121657512924659 74806357203182486269386989)
      ·
        refine ⟨28052383951193432351020121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74806357203182486269386989 28052383951193432351020121)
        ·
          refine ⟨21039287963395074263265091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28052383951193432351020121 21039287963395074263265091)
          ·
            refine ⟨31558931945092611394897637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21039287963395074263265091 31558931945092611394897637)
            ·
              refine ⟨5917299739704864636543307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31558931945092611394897637 5917299739704864636543307)
              ·
                refine ⟨8875949609557296954814961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917299739704864636543307 8875949609557296954814961)
                ·
                  refine ⟨6656962207167972716111221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8875949609557296954814961 6656962207167972716111221)
                  ·
                    refine ⟨624090206921997442135427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6656962207167972716111221 624090206921997442135427)
                    ·
                      rfl

theorem cell23_3646234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_3646234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646234 prefixEnd_3646234 := by exact prefixLift 3646234
  have htrace : WordTrace (prefixWord ++ tailWord_3646234) baseStart_3646234 baseEnd_3646234 := by
    simpa [prefixWord, tailWord_3646234, baseEnd_3646234] using wordTrace_append hprefix tailTrace_3646234
  have hstable : (prefixWord ++ tailWord_3646234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646234).length < 2 ^ (prefixWord ++ tailWord_3646234).sum := by decide
  have hdescent : baseEnd_3646234 < baseStart_3646234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646257 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_3646257 : Nat := 118140960795 + 3646257 * 2 ^ 59
def prefixEnd_3646257 : Nat := 4983230072969 + 3 ^ 40 * 3646257 * 2
def baseEnd_3646257 : Nat := 1872282430821045736418675

theorem tailTrace_3646257 : CollatzResearch.WordTrace tailWord_3646257 prefixEnd_3646257 1872282430821045736418675 := by
  unfold tailWord_3646257
  simp only [CollatzResearch.WordTrace]
  refine ⟨132989918351241094962553025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88659945567494063308368683 132989918351241094962553025)
  ·
    refine ⟨99742438763430821221914769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132989918351241094962553025 99742438763430821221914769)
    ·
      refine ⟨74806829072573115916436077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99742438763430821221914769 74806829072573115916436077)
      ·
        refine ⟨28052560902214918468663529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74806829072573115916436077 28052560902214918468663529)
        ·
          refine ⟨21039420676661188851497647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28052560902214918468663529 21039420676661188851497647)
          ·
            refine ⟨31559131014991783277246471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21039420676661188851497647 31559131014991783277246471)
            ·
              refine ⟨47338696522487674915869707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31559131014991783277246471 47338696522487674915869707)
              ·
                refine ⟨71008044783731512373804561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47338696522487674915869707 71008044783731512373804561)
                ·
                  refine ⟨53256033587798634280353421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71008044783731512373804561 53256033587798634280353421)
                  ·
                    refine ⟨19971012595424487855132533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53256033587798634280353421 19971012595424487855132533)
                    ·
                      refine ⟨1872282430821045736418675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19971012595424487855132533 1872282430821045736418675)
                      ·
                        rfl

theorem cell23_3646257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_3646257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646257 prefixEnd_3646257 := by exact prefixLift 3646257
  have htrace : WordTrace (prefixWord ++ tailWord_3646257) baseStart_3646257 baseEnd_3646257 := by
    simpa [prefixWord, tailWord_3646257, baseEnd_3646257] using wordTrace_append hprefix tailTrace_3646257
  have hstable : (prefixWord ++ tailWord_3646257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646257).length < 2 ^ (prefixWord ++ tailWord_3646257).sum := by decide
  have hdescent : baseEnd_3646257 < baseStart_3646257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646264 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 3, 4]
def baseStart_3646264 : Nat := 118140960795 + 3646264 * 2 ^ 59
def prefixEnd_3646264 : Nat := 4983230072969 + 3 ^ 40 * 3646264 * 2
def baseEnd_3646264 : Nat := 624095341728542403010381

theorem tailTrace_3646264 : CollatzResearch.WordTrace tailWord_3646264 prefixEnd_3646264 624095341728542403010381 := by
  unfold tailWord_3646264
  simp only [CollatzResearch.WordTrace]
  refine ⟨66495086831107867579028923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88660115774810490105371897 66495086831107867579028923)
  ·
    refine ⟨99742630246661801368543385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66495086831107867579028923 99742630246661801368543385)
    ·
      refine ⟨74806972684996351026407539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99742630246661801368543385 74806972684996351026407539)
      ·
        refine ⟨112210459027494526539611309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74806972684996351026407539 112210459027494526539611309)
        ·
          refine ⟨42078922135310447452354241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112210459027494526539611309 42078922135310447452354241)
          ·
            refine ⟨31559191601482835589265681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42078922135310447452354241 31559191601482835589265681)
            ·
              refine ⟨23669393701112126691949261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31559191601482835589265681 23669393701112126691949261)
              ·
                refine ⟨8876022637917047509480973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23669393701112126691949261 8876022637917047509480973)
                ·
                  refine ⟨3328508489218892816055365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8876022637917047509480973 3328508489218892816055365)
                  ·
                    refine ⟨624095341728542403010381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3328508489218892816055365 624095341728542403010381)
                    ·
                      rfl

theorem cell23_3646264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_3646264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646264 prefixEnd_3646264 := by exact prefixLift 3646264
  have htrace : WordTrace (prefixWord ++ tailWord_3646264) baseStart_3646264 baseEnd_3646264 := by
    simpa [prefixWord, tailWord_3646264, baseEnd_3646264] using wordTrace_append hprefix tailTrace_3646264
  have hstable : (prefixWord ++ tailWord_3646264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646264).length < 2 ^ (prefixWord ++ tailWord_3646264).sum := by decide
  have hdescent : baseEnd_3646264 < baseStart_3646264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646271 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 2, 4, 2]
def baseStart_3646271 : Nat := 118140960795 + 3646271 * 2 ^ 59
def prefixEnd_3646271 : Nat := 4983230072969 + 3 ^ 40 * 3646271 * 2
def baseEnd_3646271 : Nat := 1872289619550208681643611

theorem tailTrace_3646271 : CollatzResearch.WordTrace tailWord_3646271 prefixEnd_3646271 1872289619550208681643611 := by
  unfold tailWord_3646271
  simp only [CollatzResearch.WordTrace]
  refine ⟨132990428973190375353562667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88660285982126916902375111 132990428973190375353562667)
  ·
    refine ⟨199485643459785563030344001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132990428973190375353562667 199485643459785563030344001)
    ·
      refine ⟨149614232594839172272758001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199485643459785563030344001 149614232594839172272758001)
      ·
        refine ⟨112210674446129379204568501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149614232594839172272758001 112210674446129379204568501)
        ·
          refine ⟨10519750729324629300428297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112210674446129379204568501 10519750729324629300428297)
          ·
            refine ⟨7889813046993471975321223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10519750729324629300428297 7889813046993471975321223)
            ·
              refine ⟨11834719570490207962981835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7889813046993471975321223 11834719570490207962981835)
              ·
                refine ⟨17752079355735311944472753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11834719570490207962981835 17752079355735311944472753)
                ·
                  refine ⟨13314059516801483958354565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17752079355735311944472753 13314059516801483958354565)
                  ·
                    refine ⟨2496386159400278242191481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13314059516801483958354565 2496386159400278242191481)
                    ·
                      refine ⟨1872289619550208681643611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496386159400278242191481 1872289619550208681643611)
                      ·
                        rfl

theorem cell23_3646271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 4, 2].length) (baseStart_3646271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646271 prefixEnd_3646271 := by exact prefixLift 3646271
  have htrace : WordTrace (prefixWord ++ tailWord_3646271) baseStart_3646271 baseEnd_3646271 := by
    simpa [prefixWord, tailWord_3646271, baseEnd_3646271] using wordTrace_append hprefix tailTrace_3646271
  have hstable : (prefixWord ++ tailWord_3646271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646271).length < 2 ^ (prefixWord ++ tailWord_3646271).sum := by decide
  have hdescent : baseEnd_3646271 < baseStart_3646271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646285 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_3646285 : Nat := 118140960795 + 3646285 * 2 ^ 59
def prefixEnd_3646285 : Nat := 4983230072969 + 3 ^ 40 * 3646285 * 2
def baseEnd_3646285 : Nat := 624098936093123875622849

theorem tailTrace_3646285 : CollatzResearch.WordTrace tailWord_3646285 prefixEnd_3646285 624098936093123875622849 := by
  unfold tailWord_3646285
  simp only [CollatzResearch.WordTrace]
  refine ⟨132990939595139655744572309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88660626396759770496381539 132990939595139655744572309)
  ·
    refine ⟨6233950293522171363026827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132990939595139655744572309 6233950293522171363026827)
    ·
      refine ⟨9350925440283257044540241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6233950293522171363026827 9350925440283257044540241)
      ·
        refine ⟨7013194080212442783405181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9350925440283257044540241 7013194080212442783405181)
        ·
          refine ⟨2629947780079666043776943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7013194080212442783405181 2629947780079666043776943)
          ·
            refine ⟨3944921670119499065665415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2629947780079666043776943 3944921670119499065665415)
            ·
              refine ⟨5917382505179248598498123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944921670119499065665415 5917382505179248598498123)
              ·
                refine ⟨8876073757768872897747185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5917382505179248598498123 8876073757768872897747185)
                ·
                  refine ⟨6657055318326654673310389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8876073757768872897747185 6657055318326654673310389)
                  ·
                    refine ⟨624098936093123875622849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6657055318326654673310389 624098936093123875622849)
                    ·
                      rfl

theorem cell23_3646285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_3646285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646285 prefixEnd_3646285 := by exact prefixLift 3646285
  have htrace : WordTrace (prefixWord ++ tailWord_3646285) baseStart_3646285 baseEnd_3646285 := by
    simpa [prefixWord, tailWord_3646285, baseEnd_3646285] using wordTrace_append hprefix tailTrace_3646285
  have hstable : (prefixWord ++ tailWord_3646285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646285).length < 2 ^ (prefixWord ++ tailWord_3646285).sum := by decide
  have hdescent : baseEnd_3646285 < baseStart_3646285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646298 : List Nat := [3, 1, 1, 2, 1, 5, 2, 3, 1, 4]
def baseStart_3646298 : Nat := 118140960795 + 3646298 * 2 ^ 59
def prefixEnd_3646298 : Nat := 4983230072969 + 3 ^ 40 * 3646298 * 2
def baseEnd_3646298 : Nat := 624101161175960025335329

theorem tailTrace_3646298 : CollatzResearch.WordTrace tailWord_3646298 prefixEnd_3646298 624101161175960025335329 := by
  unfold tailWord_3646298
  simp only [CollatzResearch.WordTrace]
  refine ⟨33247853436023139741198887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88660942496061705976530365 33247853436023139741198887)
  ·
    refine ⟨49871780154034709611798331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33247853436023139741198887 49871780154034709611798331)
    ·
      refine ⟨74807670231052064417697497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49871780154034709611798331 74807670231052064417697497)
      ·
        refine ⟨56105752673289048313273123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74807670231052064417697497 56105752673289048313273123)
        ·
          refine ⟨84158629009933572469909685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56105752673289048313273123 84158629009933572469909685)
          ·
            refine ⟨7889871469681272419054033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84158629009933572469909685 7889871469681272419054033)
            ·
              refine ⟨5917403602260954314290525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7889871469681272419054033 5917403602260954314290525)
              ·
                refine ⟨2219026350847857867858947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5917403602260954314290525 2219026350847857867858947)
                ·
                  refine ⟨3328539526271786801788421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219026350847857867858947 3328539526271786801788421)
                  ·
                    refine ⟨624101161175960025335329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3328539526271786801788421 624101161175960025335329)
                    ·
                      rfl

theorem cell23_3646298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_3646298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646298 prefixEnd_3646298 := by exact prefixLift 3646298
  have htrace : WordTrace (prefixWord ++ tailWord_3646298) baseStart_3646298 baseEnd_3646298 := by
    simpa [prefixWord, tailWord_3646298, baseEnd_3646298] using wordTrace_append hprefix tailTrace_3646298
  have hstable : (prefixWord ++ tailWord_3646298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646298).length < 2 ^ (prefixWord ++ tailWord_3646298).sum := by decide
  have hdescent : baseEnd_3646298 < baseStart_3646298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646311 : List Nat := [1, 1, 5, 1, 2, 4, 1, 2, 6]
def baseStart_3646311 : Nat := 118140960795 + 3646311 * 2 ^ 59
def prefixEnd_3646311 : Nat := 4983230072969 + 3 ^ 40 * 3646311 * 2
def baseEnd_3646311 : Nat := 208034462086265391682603

theorem tailTrace_3646311 : CollatzResearch.WordTrace tailWord_3646311 prefixEnd_3646311 208034462086265391682603 := by
  unfold tailWord_3646311
  simp only [CollatzResearch.WordTrace]
  refine ⟨132991887893045462185018787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88661258595363641456679191 132991887893045462185018787)
  ·
    refine ⟨199487831839568193277528181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132991887893045462185018787 199487831839568193277528181)
    ·
      refine ⟨18701984234959518119768267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199487831839568193277528181 18701984234959518119768267)
      ·
        refine ⟨28052976352439277179652401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18701984234959518119768267 28052976352439277179652401)
        ·
          refine ⟨21039732264329457884739301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28052976352439277179652401 21039732264329457884739301)
          ·
            refine ⟨3944949799561773353388619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21039732264329457884739301 3944949799561773353388619)
            ·
              refine ⟨5917424699342660030082929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3944949799561773353388619 5917424699342660030082929)
              ·
                refine ⟨4438068524506995022562197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5917424699342660030082929 4438068524506995022562197)
                ·
                  refine ⟨208034462086265391682603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4438068524506995022562197 208034462086265391682603)
                  ·
                    rfl

theorem cell23_3646311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 6].length) (baseStart_3646311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646311 prefixEnd_3646311 := by exact prefixLift 3646311
  have htrace : WordTrace (prefixWord ++ tailWord_3646311) baseStart_3646311 baseEnd_3646311 := by
    simpa [prefixWord, tailWord_3646311, baseEnd_3646311] using wordTrace_append hprefix tailTrace_3646311
  have hstable : (prefixWord ++ tailWord_3646311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646311).length < 2 ^ (prefixWord ++ tailWord_3646311).sum := by decide
  have hdescent : baseEnd_3646311 < baseStart_3646311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646321 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 3, 1, 3]
def baseStart_3646321 : Nat := 118140960795 + 3646321 * 2 ^ 59
def prefixEnd_3646321 : Nat := 4983230072969 + 3 ^ 40 * 3646321 * 2
def baseEnd_3646321 : Nat := 1872315293582933486018381

theorem tailTrace_3646321 : CollatzResearch.WordTrace tailWord_3646321 prefixEnd_3646321 1872315293582933486018381 := by
  unfold tailWord_3646321
  simp only [CollatzResearch.WordTrace]
  refine ⟨132992252623009233892882817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88661501748672822595255211 132992252623009233892882817)
  ·
    refine ⟨99744189467256925419662113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132992252623009233892882817 99744189467256925419662113)
    ·
      refine ⟨74808142100442694064746585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99744189467256925419662113 74808142100442694064746585)
      ·
        refine ⟨56106106575332020548559939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74808142100442694064746585 56106106575332020548559939)
        ·
          refine ⟨84159159862998030822839909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56106106575332020548559939 84159159862998030822839909)
          ·
            refine ⟨15779842474312130779282483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84159159862998030822839909 15779842474312130779282483)
            ·
              refine ⟨23669763711468196168923725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15779842474312130779282483 23669763711468196168923725)
              ·
                refine ⟨8876161391800573563346397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23669763711468196168923725 8876161391800573563346397)
                ·
                  refine ⟨3328560521925215086254899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8876161391800573563346397 3328560521925215086254899)
                  ·
                    refine ⟨4992840782887822629382349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3328560521925215086254899 4992840782887822629382349)
                    ·
                      refine ⟨1872315293582933486018381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4992840782887822629382349 1872315293582933486018381)
                      ·
                        rfl

theorem cell23_3646321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_3646321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646321 prefixEnd_3646321 := by exact prefixLift 3646321
  have htrace : WordTrace (prefixWord ++ tailWord_3646321) baseStart_3646321 baseEnd_3646321 := by
    simpa [prefixWord, tailWord_3646321, baseEnd_3646321] using wordTrace_append hprefix tailTrace_3646321
  have hstable : (prefixWord ++ tailWord_3646321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646321).length < 2 ^ (prefixWord ++ tailWord_3646321).sum := by decide
  have hdescent : baseEnd_3646321 < baseStart_3646321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646341 : List Nat := [1, 3, 1, 1, 3, 4, 2, 2, 1, 5]
def baseStart_3646341 : Nat := 118140960795 + 3646341 * 2 ^ 59
def prefixEnd_3646341 : Nat := 4983230072969 + 3 ^ 40 * 3646341 * 2
def baseEnd_3646341 : Nat := 624108521065341135922763

theorem tailTrace_3646341 : CollatzResearch.WordTrace tailWord_3646341 prefixEnd_3646341 624108521065341135922763 := by
  unfold tailWord_3646341
  simp only [CollatzResearch.WordTrace]
  refine ⟨132992982082936777308610877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88661988055291184872407251 132992982082936777308610877)
  ·
    refine ⟨49872368281101291490729079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132992982082936777308610877 49872368281101291490729079)
    ·
      refine ⟨74808552421651937236093619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49872368281101291490729079 74808552421651937236093619)
      ·
        refine ⟨112212828632477905854140429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74808552421651937236093619 112212828632477905854140429)
        ·
          refine ⟨42079810737179214695302661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112212828632477905854140429 42079810737179214695302661)
          ·
            refine ⟨7889964513221102755369249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42079810737179214695302661 7889964513221102755369249)
            ·
              refine ⟨5917473384915827066526937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7889964513221102755369249 5917473384915827066526937)
              ·
                refine ⟨4438105038686870299895203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5917473384915827066526937 4438105038686870299895203)
                ·
                  refine ⟨6657157558030305449842805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4438105038686870299895203 6657157558030305449842805)
                  ·
                    refine ⟨624108521065341135922763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6657157558030305449842805 624108521065341135922763)
                    ·
                      rfl

theorem cell23_3646341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_3646341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646341 prefixEnd_3646341 := by exact prefixLift 3646341
  have htrace : WordTrace (prefixWord ++ tailWord_3646341) baseStart_3646341 baseEnd_3646341 := by
    simpa [prefixWord, tailWord_3646341, baseEnd_3646341] using wordTrace_append hprefix tailTrace_3646341
  have hstable : (prefixWord ++ tailWord_3646341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646341).length < 2 ^ (prefixWord ++ tailWord_3646341).sum := by decide
  have hdescent : baseEnd_3646341 < baseStart_3646341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646411 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 3]
def baseStart_3646411 : Nat := 118140960795 + 3646411 * 2 ^ 59
def prefixEnd_3646411 : Nat := 4983230072969 + 3 ^ 40 * 3646411 * 2
def baseEnd_3646411 : Nat := 1872361506841838133892967

theorem tailTrace_3646411 : CollatzResearch.WordTrace tailWord_3646411 prefixEnd_3646411 1872361506841838133892967 := by
  unfold tailWord_3646411
  simp only [CollatzResearch.WordTrace]
  refine ⟨132995535192683179263659087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88663690128455452842439391 132995535192683179263659087)
  ·
    refine ⟨199493302789024768895488631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132995535192683179263659087 199493302789024768895488631)
    ·
      refine ⟨299239954183537153343232947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199493302789024768895488631 299239954183537153343232947)
      ·
        refine ⟨448859931275305730014849421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299239954183537153343232947 448859931275305730014849421)
        ·
          refine ⟨168322474228239648755568533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448859931275305730014849421 168322474228239648755568533)
          ·
            refine ⟨7890115979448733535417275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168322474228239648755568533 7890115979448733535417275)
            ·
              refine ⟨11835173969173100303125913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7890115979448733535417275 11835173969173100303125913)
              ·
                refine ⟨8876380476879825227344435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11835173969173100303125913 8876380476879825227344435)
                ·
                  refine ⟨13314570715319737841016653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8876380476879825227344435 13314570715319737841016653)
                  ·
                    refine ⟨4992964018244901690381245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13314570715319737841016653 4992964018244901690381245)
                    ·
                      refine ⟨1872361506841838133892967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4992964018244901690381245 1872361506841838133892967)
                      ·
                        rfl

theorem cell23_3646411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 3].length) (baseStart_3646411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646411 prefixEnd_3646411 := by exact prefixLift 3646411
  have htrace : WordTrace (prefixWord ++ tailWord_3646411) baseStart_3646411 baseEnd_3646411 := by
    simpa [prefixWord, tailWord_3646411, baseEnd_3646411] using wordTrace_append hprefix tailTrace_3646411
  have hstable : (prefixWord ++ tailWord_3646411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646411).length < 2 ^ (prefixWord ++ tailWord_3646411).sum := by decide
  have hdescent : baseEnd_3646411 < baseStart_3646411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646429 : List Nat := [1, 4, 3, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_3646429 : Nat := 118140960795 + 3646429 * 2 ^ 59
def prefixEnd_3646429 : Nat := 4983230072969 + 3 ^ 40 * 3646429 * 2
def baseEnd_3646429 : Nat := 1872370749493619063467885

theorem tailTrace_3646429 : CollatzResearch.WordTrace tailWord_3646429 prefixEnd_3646429 1872370749493619063467885 := by
  unfold tailWord_3646429
  simp only [CollatzResearch.WordTrace]
  refine ⟨132996191706617968337814341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88664127804411978891876227 132996191706617968337814341)
  ·
    refine ⟨24936785944990869063340189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132996191706617968337814341 24936785944990869063340189)
    ·
      refine ⟨9351294729371575898752571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24936785944990869063340189 9351294729371575898752571)
      ·
        refine ⟨14026942094057363848128857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9351294729371575898752571 14026942094057363848128857)
        ·
          refine ⟨10520206570543022886096643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14026942094057363848128857 10520206570543022886096643)
          ·
            refine ⟨15780309855814534329144965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10520206570543022886096643 15780309855814534329144965)
            ·
              refine ⟨2958808097965225186714681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15780309855814534329144965 2958808097965225186714681)
              ·
                refine ⟨2219106073473918890036011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2958808097965225186714681 2219106073473918890036011)
                ·
                  refine ⟨3328659110210878335054017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219106073473918890036011 3328659110210878335054017)
                  ·
                    refine ⟨2496494332658158751290513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3328659110210878335054017 2496494332658158751290513)
                    ·
                      refine ⟨1872370749493619063467885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496494332658158751290513 1872370749493619063467885)
                      ·
                        rfl

theorem cell23_3646429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_3646429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646429 prefixEnd_3646429 := by exact prefixLift 3646429
  have htrace : WordTrace (prefixWord ++ tailWord_3646429) baseStart_3646429 baseEnd_3646429 := by
    simpa [prefixWord, tailWord_3646429, baseEnd_3646429] using wordTrace_append hprefix tailTrace_3646429
  have hstable : (prefixWord ++ tailWord_3646429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646429).length < 2 ^ (prefixWord ++ tailWord_3646429).sum := by decide
  have hdescent : baseEnd_3646429 < baseStart_3646429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646466 : List Nat := [3, 4, 1, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_3646466 : Nat := 118140960795 + 3646466 * 2 ^ 59
def prefixEnd_3646466 : Nat := 4983230072969 + 3 ^ 40 * 3646466 * 2
def baseEnd_3646466 : Nat := 1872389748277835418705215

theorem tailTrace_3646466 : CollatzResearch.WordTrace tailWord_3646466 prefixEnd_3646466 1872389748277835418705215 := by
  unfold tailWord_3646466
  simp only [CollatzResearch.WordTrace]
  refine ⟨33249385301870980914227813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88665027471655949104607501 33249385301870980914227813)
  ·
    refine ⟨6234259744100808921417715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33249385301870980914227813 6234259744100808921417715)
    ·
      refine ⟨9351389616151213382126573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6234259744100808921417715 9351389616151213382126573)
      ·
        refine ⟨3506771106056705018297465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9351389616151213382126573 3506771106056705018297465)
        ·
          refine ⟨2630078329542528763723099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3506771106056705018297465 2630078329542528763723099)
          ·
            refine ⟨3945117494313793145584649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630078329542528763723099 3945117494313793145584649)
            ·
              refine ⟨2958838120735344859188487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3945117494313793145584649 2958838120735344859188487)
              ·
                refine ⟨4438257181103017288782731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958838120735344859188487 4438257181103017288782731)
                ·
                  refine ⟨6657385771654525933174097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4438257181103017288782731 6657385771654525933174097)
                  ·
                    refine ⟨4993039328740894449880573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6657385771654525933174097 4993039328740894449880573)
                    ·
                      refine ⟨1872389748277835418705215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4993039328740894449880573 1872389748277835418705215)
                      ·
                        rfl

theorem cell23_3646466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_3646466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646466 prefixEnd_3646466 := by exact prefixLift 3646466
  have htrace : WordTrace (prefixWord ++ tailWord_3646466) baseStart_3646466 baseEnd_3646466 := by
    simpa [prefixWord, tailWord_3646466, baseEnd_3646466] using wordTrace_append hprefix tailTrace_3646466
  have hstable : (prefixWord ++ tailWord_3646466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646466).length < 2 ^ (prefixWord ++ tailWord_3646466).sum := by decide
  have hdescent : baseEnd_3646466 < baseStart_3646466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646472 : List Nat := [2, 1, 3, 2, 1, 5, 2, 1, 1, 3, 2]
def baseStart_3646472 : Nat := 118140960795 + 3646472 * 2 ^ 59
def prefixEnd_3646472 : Nat := 4983230072969 + 3 ^ 40 * 3646472 * 2
def baseEnd_3646472 : Nat := 1872392829161762395230187

theorem tailTrace_3646472 : CollatzResearch.WordTrace tailWord_3646472 prefixEnd_3646472 1872392829161762395230187 := by
  unfold tailWord_3646472
  simp only [CollatzResearch.WordTrace]
  refine ⟨66498880022731093340814835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88665173363641457787753113 66498880022731093340814835)
  ·
    refine ⟨99748320034096640011222253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66498880022731093340814835 99748320034096640011222253)
    ·
      refine ⟨37405620012786240004208345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99748320034096640011222253 37405620012786240004208345)
      ·
        refine ⟨28054215009589680003156259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37405620012786240004208345 28054215009589680003156259)
        ·
          refine ⟨42081322514384520004734389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28054215009589680003156259 42081322514384520004734389)
          ·
            refine ⟨3945123985723548750443849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42081322514384520004734389 3945123985723548750443849)
            ·
              refine ⟨2958842989292661562832887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3945123985723548750443849 2958842989292661562832887)
              ·
                refine ⟨4438264483938992344249331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2958842989292661562832887 4438264483938992344249331)
                ·
                  refine ⟨6657396725908488516373997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4438264483938992344249331 6657396725908488516373997)
                  ·
                    refine ⟨2496523772215683193640249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6657396725908488516373997 2496523772215683193640249)
                    ·
                      refine ⟨1872392829161762395230187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496523772215683193640249 1872392829161762395230187)
                      ·
                        rfl

theorem cell23_3646472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_3646472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646472 prefixEnd_3646472 := by exact prefixLift 3646472
  have htrace : WordTrace (prefixWord ++ tailWord_3646472) baseStart_3646472 baseEnd_3646472 := by
    simpa [prefixWord, tailWord_3646472, baseEnd_3646472] using wordTrace_append hprefix tailTrace_3646472
  have hstable : (prefixWord ++ tailWord_3646472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646472).length < 2 ^ (prefixWord ++ tailWord_3646472).sum := by decide
  have hdescent : baseEnd_3646472 < baseStart_3646472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646485 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 4, 2, 2]
def baseStart_3646485 : Nat := 118140960795 + 3646485 * 2 ^ 59
def prefixEnd_3646485 : Nat := 4983230072969 + 3 ^ 40 * 3646485 * 2
def baseEnd_3646485 : Nat := 1872399504410270844367627

theorem tailTrace_3646485 : CollatzResearch.WordTrace tailWord_3646485 prefixEnd_3646485 1872399504410270844367627 := by
  unfold tailWord_3646485
  simp only [CollatzResearch.WordTrace]
  refine ⟨132998234194415089901852909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88665489462943393267901939 132998234194415089901852909)
  ·
    refine ⟨49874337822905658713194841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132998234194415089901852909 49874337822905658713194841)
    ·
      refine ⟨37405753367179244034896131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49874337822905658713194841 37405753367179244034896131)
      ·
        refine ⟨56108630050768866052344197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37405753367179244034896131 56108630050768866052344197)
        ·
          refine ⟨10520368134519162384814537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56108630050768866052344197 10520368134519162384814537)
          ·
            refine ⟨7890276100889371788610903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10520368134519162384814537 7890276100889371788610903)
            ·
              refine ⟨11835414151334057682916355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7890276100889371788610903 11835414151334057682916355)
              ·
                refine ⟨17753121227001086524374533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11835414151334057682916355 17753121227001086524374533)
                ·
                  refine ⟨3328710230062703723320225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17753121227001086524374533 3328710230062703723320225)
                  ·
                    refine ⟨2496532672547027792490169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3328710230062703723320225 2496532672547027792490169)
                    ·
                      refine ⟨1872399504410270844367627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496532672547027792490169 1872399504410270844367627)
                      ·
                        rfl

theorem cell23_3646485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_3646485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646485 prefixEnd_3646485 := by exact prefixLift 3646485
  have htrace : WordTrace (prefixWord ++ tailWord_3646485) baseStart_3646485 baseEnd_3646485 := by
    simpa [prefixWord, tailWord_3646485, baseEnd_3646485] using wordTrace_append hprefix tailTrace_3646485
  have hstable : (prefixWord ++ tailWord_3646485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646485).length < 2 ^ (prefixWord ++ tailWord_3646485).sum := by decide
  have hdescent : baseEnd_3646485 < baseStart_3646485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646501 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 2, 3, 3]
def baseStart_3646501 : Nat := 118140960795 + 3646501 * 2 ^ 59
def prefixEnd_3646501 : Nat := 4983230072969 + 3 ^ 40 * 3646501 * 2
def baseEnd_3646501 : Nat := 1872407720100742781767553

theorem tailTrace_3646501 : CollatzResearch.WordTrace tailWord_3646501 prefixEnd_3646501 1872407720100742781767553 := by
  unfold tailWord_3646501
  simp only [CollatzResearch.WordTrace]
  refine ⟨132998817762357124634435357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88665878508238083089623571 132998817762357124634435357)
  ·
    refine ⟨49874556660883921737913259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132998817762357124634435357 49874556660883921737913259)
    ·
      refine ⟨74811834991325882606869889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49874556660883921737913259 74811834991325882606869889)
      ·
        refine ⟨56108876243494411955152417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74811834991325882606869889 56108876243494411955152417)
        ·
          refine ⟨42081657182620808966364313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56108876243494411955152417 42081657182620808966364313)
          ·
            refine ⟨31561242886965606724773235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42081657182620808966364313 31561242886965606724773235)
            ·
              refine ⟨47341864330448410087159853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31561242886965606724773235 47341864330448410087159853)
              ·
                refine ⟨17753199123918153782684945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47341864330448410087159853 17753199123918153782684945)
                ·
                  refine ⟨13314899342938615337013709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17753199123918153782684945 13314899342938615337013709)
                  ·
                    refine ⟨4993087253601980751380141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13314899342938615337013709 4993087253601980751380141)
                    ·
                      refine ⟨1872407720100742781767553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4993087253601980751380141 1872407720100742781767553)
                      ·
                        rfl

theorem cell23_3646501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_3646501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646501 prefixEnd_3646501 := by exact prefixLift 3646501
  have htrace : WordTrace (prefixWord ++ tailWord_3646501) baseStart_3646501 baseEnd_3646501 := by
    simpa [prefixWord, tailWord_3646501, baseEnd_3646501] using wordTrace_append hprefix tailTrace_3646501
  have hstable : (prefixWord ++ tailWord_3646501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646501).length < 2 ^ (prefixWord ++ tailWord_3646501).sum := by decide
  have hdescent : baseEnd_3646501 < baseStart_3646501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646511 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 3, 7, 2]
def baseStart_3646511 : Nat := 118140960795 + 3646511 * 2 ^ 59
def prefixEnd_3646511 : Nat := 4983230072969 + 3 ^ 40 * 3646511 * 2
def baseEnd_3646511 : Nat := 1872412854907287742642507

theorem tailTrace_3646511 : CollatzResearch.WordTrace tailWord_3646511 prefixEnd_3646511 1872412854907287742642507 := by
  unfold tailWord_3646511
  simp only [CollatzResearch.WordTrace]
  refine ⟨132999182492320896342299387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88666121661547264228199591 132999182492320896342299387)
  ·
    refine ⟨199498773738481344513449081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132999182492320896342299387 199498773738481344513449081)
    ·
      refine ⟨149624080303861008385086811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199498773738481344513449081 149624080303861008385086811)
      ·
        refine ⟨224436120455791512577630217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149624080303861008385086811 224436120455791512577630217)
        ·
          refine ⟨168327090341843634433222663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224436120455791512577630217 168327090341843634433222663)
          ·
            refine ⟨252490635512765451649833995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168327090341843634433222663 252490635512765451649833995)
            ·
              refine ⟨378735953269148177474750993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252490635512765451649833995 378735953269148177474750993)
              ·
                refine ⟨284051964951861133106063245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378735953269148177474750993 284051964951861133106063245)
                ·
                  refine ⟨106519486856947924914773717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284051964951861133106063245 106519486856947924914773717)
                  ·
                    refine ⟨2496550473209716990190009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 106519486856947924914773717 2496550473209716990190009)
                    ·
                      refine ⟨1872412854907287742642507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496550473209716990190009 1872412854907287742642507)
                      ·
                        rfl

theorem cell23_3646511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 7, 2].length) (baseStart_3646511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646511 prefixEnd_3646511 := by exact prefixLift 3646511
  have htrace : WordTrace (prefixWord ++ tailWord_3646511) baseStart_3646511 baseEnd_3646511 := by
    simpa [prefixWord, tailWord_3646511, baseEnd_3646511] using wordTrace_append hprefix tailTrace_3646511
  have hstable : (prefixWord ++ tailWord_3646511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646511).length < 2 ^ (prefixWord ++ tailWord_3646511).sum := by decide
  have hdescent : baseEnd_3646511 < baseStart_3646511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646521 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 1, 7]
def baseStart_3646521 : Nat := 118140960795 + 3646521 * 2 ^ 59
def prefixEnd_3646521 : Nat := 4983230072969 + 3 ^ 40 * 3646521 * 2
def baseEnd_3646521 : Nat := 624139329904610901172487

theorem tailTrace_3646521 : CollatzResearch.WordTrace tailWord_3646521 prefixEnd_3646521 624139329904610901172487 := by
  unfold tailWord_3646521
  simp only [CollatzResearch.WordTrace]
  refine ⟨132999547222284668050163417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88666364814856445366775611 132999547222284668050163417)
  ·
    refine ⟨99749660416713501037622563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132999547222284668050163417 99749660416713501037622563)
    ·
      refine ⟨149624490625070251556433845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99749660416713501037622563 149624490625070251556433845)
      ·
        refine ⟨14027295996100336083415673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149624490625070251556433845 14027295996100336083415673)
        ·
          refine ⟨10520471997075252062561755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14027295996100336083415673 10520471997075252062561755)
          ·
            refine ⟨15780707995612878093842633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10520471997075252062561755 15780707995612878093842633)
            ·
              refine ⟨11835530996709658570381975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15780707995612878093842633 11835530996709658570381975)
              ·
                refine ⟨17753296495064487855572963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11835530996709658570381975 17753296495064487855572963)
                ·
                  refine ⟨26629944742596731783359445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17753296495064487855572963 26629944742596731783359445)
                  ·
                    refine ⟨624139329904610901172487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26629944742596731783359445 624139329904610901172487)
                    ·
                      rfl

theorem cell23_3646521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_3646521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646521 prefixEnd_3646521 := by exact prefixLift 3646521
  have htrace : WordTrace (prefixWord ++ tailWord_3646521) baseStart_3646521 baseEnd_3646521 := by
    simpa [prefixWord, tailWord_3646521, baseEnd_3646521] using wordTrace_append hprefix tailTrace_3646521
  have hstable : (prefixWord ++ tailWord_3646521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646521).length < 2 ^ (prefixWord ++ tailWord_3646521).sum := by decide
  have hdescent : baseEnd_3646521 < baseStart_3646521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646525 : List Nat := [1, 4, 1, 3, 1, 4, 1, 3, 5]
def baseStart_3646525 : Nat := 118140960795 + 3646525 * 2 ^ 59
def prefixEnd_3646525 : Nat := 4983230072969 + 3 ^ 40 * 3646525 * 2
def baseEnd_3646525 : Nat := 208046671515161187540827

theorem tailTrace_3646525 : CollatzResearch.WordTrace tailWord_3646525 prefixEnd_3646525 208046671515161187540827 := by
  unfold tailWord_3646525
  simp only [CollatzResearch.WordTrace]
  refine ⟨132999693114270176733309029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88666462076180117822206019 132999693114270176733309029)
  ·
    refine ⟨24937442458925658137495443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132999693114270176733309029 24937442458925658137495443)
    ·
      refine ⟨37406163688388487206243165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24937442458925658137495443 37406163688388487206243165)
      ·
        refine ⟨14027311383145682702341187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37406163688388487206243165 14027311383145682702341187)
        ·
          refine ⟨21040967074718524053511781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14027311383145682702341187 21040967074718524053511781)
          ·
            refine ⟨3945181326509723260033459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21040967074718524053511781 3945181326509723260033459)
            ·
              refine ⟨5917771989764584890050189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3945181326509723260033459 5917771989764584890050189)
              ·
                refine ⟨2219164496161719333768821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5917771989764584890050189 2219164496161719333768821)
                ·
                  refine ⟨208046671515161187540827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2219164496161719333768821 208046671515161187540827)
                  ·
                    rfl

theorem cell23_3646525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_3646525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646525 prefixEnd_3646525 := by exact prefixLift 3646525
  have htrace : WordTrace (prefixWord ++ tailWord_3646525) baseStart_3646525 baseEnd_3646525 := by
    simpa [prefixWord, tailWord_3646525, baseEnd_3646525] using wordTrace_append hprefix tailTrace_3646525
  have hstable : (prefixWord ++ tailWord_3646525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646525).length < 2 ^ (prefixWord ++ tailWord_3646525).sum := by decide
  have hdescent : baseEnd_3646525 < baseStart_3646525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646561 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_3646561 : Nat := 118140960795 + 3646561 * 2 ^ 59
def prefixEnd_3646561 : Nat := 4983230072969 + 3 ^ 40 * 3646561 * 2
def baseEnd_3646561 : Nat := 1872438528940012547017277

theorem tailTrace_3646561 : CollatzResearch.WordTrace tailWord_3646561 prefixEnd_3646561 1872438528940012547017277 := by
  unfold tailWord_3646561
  simp only [CollatzResearch.WordTrace]
  refine ⟨133001006142139754881619537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88667337428093169921079691 133001006142139754881619537)
  ·
    refine ⟨99750754606604816161214653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133001006142139754881619537 99750754606604816161214653)
    ·
      refine ⟨37406532977476806060455495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99750754606604816161214653 37406532977476806060455495)
      ·
        refine ⟨56109799466215209090683243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37406532977476806060455495 56109799466215209090683243)
        ·
          refine ⟨84164699199322813636024865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56109799466215209090683243 84164699199322813636024865)
          ·
            refine ⟨63123524399492110227018649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84164699199322813636024865 63123524399492110227018649)
            ·
              refine ⟨47342643299619082670263987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63123524399492110227018649 47342643299619082670263987)
              ·
                refine ⟨71013964949428624005395981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47342643299619082670263987 71013964949428624005395981)
                ·
                  refine ⟨26630236856035734002023493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71013964949428624005395981 26630236856035734002023493)
                  ·
                    refine ⟨4993169410506700125379405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26630236856035734002023493 4993169410506700125379405)
                    ·
                      refine ⟨1872438528940012547017277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4993169410506700125379405 1872438528940012547017277)
                      ·
                        rfl

theorem cell23_3646561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_3646561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646561 prefixEnd_3646561 := by exact prefixLift 3646561
  have htrace : WordTrace (prefixWord ++ tailWord_3646561) baseStart_3646561 baseEnd_3646561 := by
    simpa [prefixWord, tailWord_3646561, baseEnd_3646561] using wordTrace_append hprefix tailTrace_3646561
  have hstable : (prefixWord ++ tailWord_3646561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646561).length < 2 ^ (prefixWord ++ tailWord_3646561).sum := by decide
  have hdescent : baseEnd_3646561 < baseStart_3646561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646611 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 3, 5]
def baseStart_3646611 : Nat := 118140960795 + 3646611 * 2 ^ 59
def prefixEnd_3646611 : Nat := 4983230072969 + 3 ^ 40 * 3646611 * 2
def baseEnd_3646611 : Nat := 624154734324245783797349

theorem tailTrace_3646611 : CollatzResearch.WordTrace tailWord_3646611 prefixEnd_3646611 624154734324245783797349 := by
  unfold tailWord_3646611
  simp only [CollatzResearch.WordTrace]
  refine ⟨133002829791958613420939687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88668553194639075613959791 133002829791958613420939687)
  ·
    refine ⟨199504244687937920131409531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133002829791958613420939687 199504244687937920131409531)
    ·
      refine ⟨299256367031906880197114297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199504244687937920131409531 299256367031906880197114297)
      ·
        refine ⟨224442275273930160147835723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299256367031906880197114297 224442275273930160147835723)
        ·
          refine ⟨336663412910895240221753585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224442275273930160147835723 336663412910895240221753585)
          ·
            refine ⟨252497559683171430166315189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336663412910895240221753585 252497559683171430166315189)
            ·
              refine ⟨23671646220297321578092049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 252497559683171430166315189 23671646220297321578092049)
              ·
                refine ⟨17753734665222991183569037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23671646220297321578092049 17753734665222991183569037)
                ·
                  refine ⟨6657650499458621693838389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17753734665222991183569037 6657650499458621693838389)
                  ·
                    refine ⟨624154734324245783797349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6657650499458621693838389 624154734324245783797349)
                    ·
                      rfl

theorem cell23_3646611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 5].length) (baseStart_3646611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646611 prefixEnd_3646611 := by exact prefixLift 3646611
  have htrace : WordTrace (prefixWord ++ tailWord_3646611) baseStart_3646611 baseEnd_3646611 := by
    simpa [prefixWord, tailWord_3646611, baseEnd_3646611] using wordTrace_append hprefix tailTrace_3646611
  have hstable : (prefixWord ++ tailWord_3646611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646611).length < 2 ^ (prefixWord ++ tailWord_3646611).sum := by decide
  have hdescent : baseEnd_3646611 < baseStart_3646611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646621 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_3646621 : Nat := 118140960795 + 3646621 * 2 ^ 59
def prefixEnd_3646621 : Nat := 4983230072969 + 3 ^ 40 * 3646621 * 2
def baseEnd_3646621 : Nat := 1872469337779282312267001

theorem tailTrace_3646621 : CollatzResearch.WordTrace tailWord_3646621 prefixEnd_3646621 1872469337779282312267001 := by
  unfold tailWord_3646621
  simp only [CollatzResearch.WordTrace]
  refine ⟨133003194521922385128803717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88668796347948256752535811 133003194521922385128803717)
  ·
    refine ⟨24938098972860447211650697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133003194521922385128803717 24938098972860447211650697)
    ·
      refine ⟨18703574229645335408738023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24938098972860447211650697 18703574229645335408738023)
      ·
        refine ⟨28055361344468003113107035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18703574229645335408738023 28055361344468003113107035)
        ·
          refine ⟨42083042016702004669660553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28055361344468003113107035 42083042016702004669660553)
          ·
            refine ⟨31562281512526503502245415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42083042016702004669660553 31562281512526503502245415)
            ·
              refine ⟨47343422268789755253368123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31562281512526503502245415 47343422268789755253368123)
              ·
                refine ⟨71015133403184632880052185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47343422268789755253368123 71015133403184632880052185)
                ·
                  refine ⟨53261350052388474660039139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71015133403184632880052185 53261350052388474660039139)
                  ·
                    refine ⟨79892025078582711990058709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53261350052388474660039139 79892025078582711990058709)
                    ·
                      refine ⟨1872469337779282312267001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79892025078582711990058709 1872469337779282312267001)
                      ·
                        rfl

theorem cell23_3646621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_3646621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646621 prefixEnd_3646621 := by exact prefixLift 3646621
  have htrace : WordTrace (prefixWord ++ tailWord_3646621) baseStart_3646621 baseEnd_3646621 := by
    simpa [prefixWord, tailWord_3646621, baseEnd_3646621] using wordTrace_append hprefix tailTrace_3646621
  have hstable : (prefixWord ++ tailWord_3646621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646621).length < 2 ^ (prefixWord ++ tailWord_3646621).sum := by decide
  have hdescent : baseEnd_3646621 < baseStart_3646621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646625 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3646625 : Nat := 118140960795 + 3646625 * 2 ^ 59
def prefixEnd_3646625 : Nat := 4983230072969 + 3 ^ 40 * 3646625 * 2
def baseEnd_3646625 : Nat := 1872471391701900296616983

theorem tailTrace_3646625 : CollatzResearch.WordTrace tailWord_3646625 prefixEnd_3646625 1872471391701900296616983 := by
  unfold tailWord_3646625
  simp only [CollatzResearch.WordTrace]
  refine ⟨133003340413907893811949329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88668893609271929207966219 133003340413907893811949329)
  ·
    refine ⟨99752505310430920358961997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133003340413907893811949329 99752505310430920358961997)
    ·
      refine ⟨37407189491411595134610749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99752505310430920358961997 37407189491411595134610749)
      ·
        refine ⟨14027696059279348175479031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37407189491411595134610749 14027696059279348175479031)
        ·
          refine ⟨21041544088919022263218547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14027696059279348175479031 21041544088919022263218547)
          ·
            refine ⟨31562316133378533394827821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21041544088919022263218547 31562316133378533394827821)
            ·
              refine ⟨11835868550016950023060433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31562316133378533394827821 11835868550016950023060433)
              ·
                refine ⟨8876901412512712517295325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11835868550016950023060433 8876901412512712517295325)
                ·
                  refine ⟨3328838029692267193985747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8876901412512712517295325 3328838029692267193985747)
                  ·
                    refine ⟨4993257044538400790978621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3328838029692267193985747 4993257044538400790978621)
                    ·
                      refine ⟨1872471391701900296616983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4993257044538400790978621 1872471391701900296616983)
                      ·
                        rfl

theorem cell23_3646625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3646625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646625 prefixEnd_3646625 := by exact prefixLift 3646625
  have htrace : WordTrace (prefixWord ++ tailWord_3646625) baseStart_3646625 baseEnd_3646625 := by
    simpa [prefixWord, tailWord_3646625, baseEnd_3646625] using wordTrace_append hprefix tailTrace_3646625
  have hstable : (prefixWord ++ tailWord_3646625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646625).length < 2 ^ (prefixWord ++ tailWord_3646625).sum := by decide
  have hdescent : baseEnd_3646625 < baseStart_3646625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646628 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 3, 5]
def baseStart_3646628 : Nat := 118140960795 + 3646628 * 2 ^ 59
def prefixEnd_3646628 : Nat := 4983230072969 + 3 ^ 40 * 3646628 * 2
def baseEnd_3646628 : Nat := 624157644047954594959823

theorem tailTrace_3646628 : CollatzResearch.WordTrace tailWord_3646628 prefixEnd_3646628 624157644047954594959823 := by
  unfold tailWord_3646628
  simp only [CollatzResearch.WordTrace]
  refine ⟨66501724916448512662154269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88668966555264683549539025 66501724916448512662154269)
  ·
    refine ⟨24938146843668192248307851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66501724916448512662154269 24938146843668192248307851)
    ·
      refine ⟨37407220265502288372461777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24938146843668192248307851 37407220265502288372461777)
      ·
        refine ⟨28055415199126716279346333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37407220265502288372461777 28055415199126716279346333)
        ·
          refine ⟨10520780699672518604754875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28055415199126716279346333 10520780699672518604754875)
          ·
            refine ⟨15781171049508777907132313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10520780699672518604754875 15781171049508777907132313)
            ·
              refine ⟨11835878287131583430349235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15781171049508777907132313 11835878287131583430349235)
              ·
                refine ⟨17753817430697375145523853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11835878287131583430349235 17753817430697375145523853)
                ·
                  refine ⟨6657681536511515679571445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17753817430697375145523853 6657681536511515679571445)
                  ·
                    refine ⟨624157644047954594959823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6657681536511515679571445 624157644047954594959823)
                    ·
                      rfl

theorem cell23_3646628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_3646628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646628 prefixEnd_3646628 := by exact prefixLift 3646628
  have htrace : WordTrace (prefixWord ++ tailWord_3646628) baseStart_3646628 baseEnd_3646628 := by
    simpa [prefixWord, tailWord_3646628, baseEnd_3646628] using wordTrace_append hprefix tailTrace_3646628
  have hstable : (prefixWord ++ tailWord_3646628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646628).length < 2 ^ (prefixWord ++ tailWord_3646628).sum := by decide
  have hdescent : baseEnd_3646628 < baseStart_3646628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646642 : List Nat := [3, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3]
def baseStart_3646642 : Nat := 118140960795 + 3646642 * 2 ^ 59
def prefixEnd_3646642 : Nat := 4983230072969 + 3 ^ 40 * 3646642 * 2
def baseEnd_3646642 : Nat := 1872480120873026730104405

theorem tailTrace_3646642 : CollatzResearch.WordTrace tailWord_3646642 prefixEnd_3646642 1872480120873026730104405 := by
  unfold tailWord_3646642
  simp only [CollatzResearch.WordTrace]
  refine ⟨33250990113711576428829545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88669306969897537143545453 33250990113711576428829545)
  ·
    refine ⟨24938242585283682321622159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33250990113711576428829545 24938242585283682321622159)
    ·
      refine ⟨37407363877925523482433239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24938242585283682321622159 37407363877925523482433239)
      ·
        refine ⟨56111045816888285223649859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37407363877925523482433239 56111045816888285223649859)
        ·
          refine ⟨84166568725332427835474789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56111045816888285223649859 84166568725332427835474789)
          ·
            refine ⟨15781231635999830219151523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84166568725332427835474789 15781231635999830219151523)
            ·
              refine ⟨23671847453999745328727285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15781231635999830219151523 23671847453999745328727285)
              ·
                refine ⟨2219235698812476124568183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23671847453999745328727285 2219235698812476124568183)
                ·
                  refine ⟨3328853548218714186852275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219235698812476124568183 3328853548218714186852275)
                  ·
                    refine ⟨4993280322328071280278413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3328853548218714186852275 4993280322328071280278413)
                    ·
                      refine ⟨1872480120873026730104405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4993280322328071280278413 1872480120873026730104405)
                      ·
                        rfl

theorem cell23_3646642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_3646642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646642 prefixEnd_3646642 := by exact prefixLift 3646642
  have htrace : WordTrace (prefixWord ++ tailWord_3646642) baseStart_3646642 baseEnd_3646642 := by
    simpa [prefixWord, tailWord_3646642, baseEnd_3646642] using wordTrace_append hprefix tailTrace_3646642
  have hstable : (prefixWord ++ tailWord_3646642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646642).length < 2 ^ (prefixWord ++ tailWord_3646642).sum := by decide
  have hdescent : baseEnd_3646642 < baseStart_3646642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646661 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_3646661 : Nat := 118140960795 + 3646661 * 2 ^ 59
def prefixEnd_3646661 : Nat := 4983230072969 + 3 ^ 40 * 3646661 * 2
def baseEnd_3646661 : Nat := 1872489877005462155766817

theorem tailTrace_3646661 : CollatzResearch.WordTrace tailWord_3646661 prefixEnd_3646661 1872489877005462155766817 := by
  unfold tailWord_3646661
  simp only [CollatzResearch.WordTrace]
  refine ⟨133004653441777471960259837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88669768961184981306839891 133004653441777471960259837)
  ·
    refine ⟨49876745040666551985097439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133004653441777471960259837 49876745040666551985097439)
    ·
      refine ⟨74815117560999827977646159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49876745040666551985097439 74815117560999827977646159)
      ·
        refine ⟨112222676341499741966469239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74815117560999827977646159 112222676341499741966469239)
        ·
          refine ⟨168334014512249612949703859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112222676341499741966469239 168334014512249612949703859)
          ·
            refine ⟨252501021768374419424555789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168334014512249612949703859 252501021768374419424555789)
            ·
              refine ⟨94687883163140407284208421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252501021768374419424555789 94687883163140407284208421)
              ·
                refine ⟨17753978093088826365789079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94687883163140407284208421 17753978093088826365789079)
                ·
                  refine ⟨26630967139633239548683619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17753978093088826365789079 26630967139633239548683619)
                  ·
                    refine ⟨39946450709449859323025429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26630967139633239548683619 39946450709449859323025429)
                    ·
                      refine ⟨1872489877005462155766817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39946450709449859323025429 1872489877005462155766817)
                      ·
                        rfl

theorem cell23_3646661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_3646661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646661 prefixEnd_3646661 := by exact prefixLift 3646661
  have htrace : WordTrace (prefixWord ++ tailWord_3646661) baseStart_3646661 baseEnd_3646661 := by
    simpa [prefixWord, tailWord_3646661, baseEnd_3646661] using wordTrace_append hprefix tailTrace_3646661
  have hstable : (prefixWord ++ tailWord_3646661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646661).length < 2 ^ (prefixWord ++ tailWord_3646661).sum := by decide
  have hdescent : baseEnd_3646661 < baseStart_3646661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646688 : List Nat := [2, 1, 1, 3, 1, 4, 4, 7]
def baseStart_3646688 : Nat := 118140960795 + 3646688 * 2 ^ 59
def prefixEnd_3646688 : Nat := 4983230072969 + 3 ^ 40 * 3646688 * 2
def baseEnd_3646688 : Nat := 69351990406782724078859

theorem tailTrace_3646688 : CollatzResearch.WordTrace tailWord_3646688 prefixEnd_3646688 69351990406782724078859 := by
  unfold tailWord_3646688
  simp only [CollatzResearch.WordTrace]
  refine ⟨66502819106339827785746359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88670425475119770380995145 66502819106339827785746359)
  ·
    refine ⟨99754228659509741678619539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66502819106339827785746359 99754228659509741678619539)
    ·
      refine ⟨149631342989264612517929309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99754228659509741678619539 149631342989264612517929309)
      ·
        refine ⟨56111753620974229694223491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149631342989264612517929309 56111753620974229694223491)
        ·
          refine ⟨84167630431461344541335237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56111753620974229694223491 84167630431461344541335237)
          ·
            refine ⟨15781430705899002101500357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84167630431461344541335237 15781430705899002101500357)
            ·
              refine ⟨2959018257356062894031317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15781430705899002101500357 2959018257356062894031317)
              ·
                refine ⟨69351990406782724078859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2959018257356062894031317 69351990406782724078859)
                ·
                  rfl

theorem cell23_3646688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 7].length) (baseStart_3646688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646688 prefixEnd_3646688 := by exact prefixLift 3646688
  have htrace : WordTrace (prefixWord ++ tailWord_3646688) baseStart_3646688 baseEnd_3646688 := by
    simpa [prefixWord, tailWord_3646688, baseEnd_3646688] using wordTrace_append hprefix tailTrace_3646688
  have hstable : (prefixWord ++ tailWord_3646688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646688).length < 2 ^ (prefixWord ++ tailWord_3646688).sum := by decide
  have hdescent : baseEnd_3646688 < baseStart_3646688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646699 : List Nat := [1, 1, 1, 1, 2, 6, 3, 3, 1, 2, 2]
def baseStart_3646699 : Nat := 118140960795 + 3646699 * 2 ^ 59
def prefixEnd_3646699 : Nat := 4983230072969 + 3 ^ 40 * 3646699 * 2
def baseEnd_3646699 : Nat := 1872509389270333007091643

theorem tailTrace_3646699 : CollatzResearch.WordTrace tailWord_3646699 prefixEnd_3646699 1872509389270333007091643 := by
  unfold tailWord_3646699
  simp only [CollatzResearch.WordTrace]
  refine ⟨133006039415639804450143151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88670692943759869633428767 133006039415639804450143151)
  ·
    refine ⟨199509059123459706675214727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133006039415639804450143151 199509059123459706675214727)
    ·
      refine ⟨299263588685189560012822091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199509059123459706675214727 299263588685189560012822091)
      ·
        refine ⟨448895383027784340019233137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299263588685189560012822091 448895383027784340019233137)
        ·
          refine ⟨336671537270838255014424853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448895383027784340019233137 336671537270838255014424853)
          ·
            refine ⟨15781478309570543203801165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 336671537270838255014424853 15781478309570543203801165)
            ·
              refine ⟨5918054366088953701425437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15781478309570543203801165 5918054366088953701425437)
              ·
                refine ⟨2219270387283357638034539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5918054366088953701425437 2219270387283357638034539)
                ·
                  refine ⟨3328905580925036457051809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219270387283357638034539 3328905580925036457051809)
                  ·
                    refine ⟨2496679185693777342788857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3328905580925036457051809 2496679185693777342788857)
                    ·
                      refine ⟨1872509389270333007091643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496679185693777342788857 1872509389270333007091643)
                      ·
                        rfl

theorem cell23_3646699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 1, 2, 2].length) (baseStart_3646699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646699 prefixEnd_3646699 := by exact prefixLift 3646699
  have htrace : WordTrace (prefixWord ++ tailWord_3646699) baseStart_3646699 baseEnd_3646699 := by
    simpa [prefixWord, tailWord_3646699, baseEnd_3646699] using wordTrace_append hprefix tailTrace_3646699
  have hstable : (prefixWord ++ tailWord_3646699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646699).length < 2 ^ (prefixWord ++ tailWord_3646699).sum := by decide
  have hdescent : baseEnd_3646699 < baseStart_3646699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646716 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 3, 2, 2]
def baseStart_3646716 : Nat := 118140960795 + 3646716 * 2 ^ 59
def prefixEnd_3646716 : Nat := 4983230072969 + 3 ^ 40 * 3646716 * 2
def baseEnd_3646716 : Nat := 1872518118441459440579065

theorem tailTrace_3646716 : CollatzResearch.WordTrace tailWord_3646716 prefixEnd_3646716 1872518118441459440579065 := by
  unfold tailWord_3646716
  simp only [CollatzResearch.WordTrace]
  refine ⟨66503329728289108176756001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88671106304385477569008001 66503329728289108176756001)
  ·
    refine ⟨49877497296216831132567001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66503329728289108176756001 49877497296216831132567001)
    ·
      refine ⟨37408122972162623349425251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49877497296216831132567001 37408122972162623349425251)
      ·
        refine ⟨56112184458243935024137877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37408122972162623349425251 56112184458243935024137877)
        ·
          refine ⟨2630258646480184454256463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56112184458243935024137877 2630258646480184454256463)
          ·
            refine ⟨3945387969720276681384695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630258646480184454256463 3945387969720276681384695)
            ·
              refine ⟨5918081954580415022077043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3945387969720276681384695 5918081954580415022077043)
              ·
                refine ⟨8877122931870622533115565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5918081954580415022077043 8877122931870622533115565)
                ·
                  refine ⟨3328921099451483449918337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8877122931870622533115565 3328921099451483449918337)
                  ·
                    refine ⟨2496690824588612587438753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3328921099451483449918337 2496690824588612587438753)
                    ·
                      refine ⟨1872518118441459440579065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496690824588612587438753 1872518118441459440579065)
                      ·
                        rfl

theorem cell23_3646716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_3646716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646716 prefixEnd_3646716 := by exact prefixLift 3646716
  have htrace : WordTrace (prefixWord ++ tailWord_3646716) baseStart_3646716 baseEnd_3646716 := by
    simpa [prefixWord, tailWord_3646716, baseEnd_3646716] using wordTrace_append hprefix tailTrace_3646716
  have hstable : (prefixWord ++ tailWord_3646716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646716).length < 2 ^ (prefixWord ++ tailWord_3646716).sum := by decide
  have hdescent : baseEnd_3646716 < baseStart_3646716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646725 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 3, 3, 2]
def baseStart_3646725 : Nat := 118140960795 + 3646725 * 2 ^ 59
def prefixEnd_3646725 : Nat := 4983230072969 + 3 ^ 40 * 3646725 * 2
def baseEnd_3646725 : Nat := 1872522739767349905366523

theorem tailTrace_3646725 : CollatzResearch.WordTrace tailWord_3646725 prefixEnd_3646725 1872522739767349905366523 := by
  unfold tailWord_3646725
  simp only [CollatzResearch.WordTrace]
  refine ⟨133006987713545610890589629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88671325142363740593726419 133006987713545610890589629)
  ·
    refine ⟨49877620392579604083971111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133006987713545610890589629 49877620392579604083971111)
    ·
      refine ⟨74816430588869406125956667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49877620392579604083971111 74816430588869406125956667)
      ·
        refine ⟨112224645883304109188935001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74816430588869406125956667 112224645883304109188935001)
        ·
          refine ⟨84168484412478081891701251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112224645883304109188935001 84168484412478081891701251)
          ·
            refine ⟨126252726618717122837551877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84168484412478081891701251 126252726618717122837551877)
            ·
              refine ⟨23672386241009460532040977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126252726618717122837551877 23672386241009460532040977)
              ·
                refine ⟨17754289680757095399030733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23672386241009460532040977 17754289680757095399030733)
                ·
                  refine ⟨6657858630283910774636525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17754289680757095399030733 6657858630283910774636525)
                  ·
                    refine ⟨2496696986356466540488697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6657858630283910774636525 2496696986356466540488697)
                    ·
                      refine ⟨1872522739767349905366523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496696986356466540488697 1872522739767349905366523)
                      ·
                        rfl

theorem cell23_3646725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 3, 2].length) (baseStart_3646725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646725 prefixEnd_3646725 := by exact prefixLift 3646725
  have htrace : WordTrace (prefixWord ++ tailWord_3646725) baseStart_3646725 baseEnd_3646725 := by
    simpa [prefixWord, tailWord_3646725, baseEnd_3646725] using wordTrace_append hprefix tailTrace_3646725
  have hstable : (prefixWord ++ tailWord_3646725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646725).length < 2 ^ (prefixWord ++ tailWord_3646725).sum := by decide
  have hdescent : baseEnd_3646725 < baseStart_3646725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646732 : List Nat := [2, 2, 1, 2, 2, 4, 1, 3, 2, 1, 3]
def baseStart_3646732 : Nat := 118140960795 + 3646732 * 2 ^ 59
def prefixEnd_3646732 : Nat := 4983230072969 + 3 ^ 40 * 3646732 * 2
def baseEnd_3646732 : Nat := 1872526334131931377978991

theorem tailTrace_3646732 : CollatzResearch.WordTrace tailWord_3646732 prefixEnd_3646732 1872526334131931377978991 := by
  unfold tailWord_3646732
  simp only [CollatzResearch.WordTrace]
  refine ⟨66503621512260125543047225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88671495349680167390729633 66503621512260125543047225)
  ·
    refine ⟨49877716134195094157285419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66503621512260125543047225 49877716134195094157285419)
    ·
      refine ⟨74816574201292641235928129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49877716134195094157285419 74816574201292641235928129)
      ·
        refine ⟨56112430650969480926946097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74816574201292641235928129 56112430650969480926946097)
        ·
          refine ⟨42084322988227110695209573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56112430650969480926946097 42084322988227110695209573)
          ·
            refine ⟨7890810560292583255351795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42084322988227110695209573 7890810560292583255351795)
            ·
              refine ⟨11836215840438874883027693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7890810560292583255351795 11836215840438874883027693)
              ·
                refine ⟨4438580940164578081135385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11836215840438874883027693 4438580940164578081135385)
                ·
                  refine ⟨3328935705123433560851539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4438580940164578081135385 3328935705123433560851539)
                  ·
                    refine ⟨4993403557685150341277309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3328935705123433560851539 4993403557685150341277309)
                    ·
                      refine ⟨1872526334131931377978991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4993403557685150341277309 1872526334131931377978991)
                      ·
                        rfl

theorem cell23_3646732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_3646732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646732 prefixEnd_3646732 := by exact prefixLift 3646732
  have htrace : WordTrace (prefixWord ++ tailWord_3646732) baseStart_3646732 baseEnd_3646732 := by
    simpa [prefixWord, tailWord_3646732, baseEnd_3646732] using wordTrace_append hprefix tailTrace_3646732
  have hstable : (prefixWord ++ tailWord_3646732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646732).length < 2 ^ (prefixWord ++ tailWord_3646732).sum := by decide
  have hdescent : baseEnd_3646732 < baseStart_3646732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646755 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 3, 4, 2]
def baseStart_3646755 : Nat := 118140960795 + 3646755 * 2 ^ 59
def prefixEnd_3646755 : Nat := 4983230072969 + 3 ^ 40 * 3646755 * 2
def baseEnd_3646755 : Nat := 1872538144186984787991385

theorem tailTrace_3646755 : CollatzResearch.WordTrace tailWord_3646755 prefixEnd_3646755 1872538144186984787991385 := by
  unfold tailWord_3646755
  simp only [CollatzResearch.WordTrace]
  refine ⟨133008081903436926014181719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88672054602291284009454479 133008081903436926014181719)
  ·
    refine ⟨199512122855155389021272579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133008081903436926014181719 199512122855155389021272579)
    ·
      refine ⟨299268184282733083531908869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199512122855155389021272579 299268184282733083531908869)
      ·
        refine ⟨56112784553012453162232913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299268184282733083531908869 56112784553012453162232913)
        ·
          refine ⟨42084588414759339871674685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56112784553012453162232913 42084588414759339871674685)
          ·
            refine ⟨15781720655534752451878007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42084588414759339871674685 15781720655534752451878007)
            ·
              refine ⟨23672580983302128677817011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15781720655534752451878007 23672580983302128677817011)
              ·
                refine ⟨35508871474953193016725517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23672580983302128677817011 35508871474953193016725517)
                ·
                  refine ⟨13315826803107447381272069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35508871474953193016725517 13315826803107447381272069)
                  ·
                    refine ⟨2496717525582646383988513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13315826803107447381272069 2496717525582646383988513)
                    ·
                      refine ⟨1872538144186984787991385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496717525582646383988513 1872538144186984787991385)
                      ·
                        rfl

theorem cell23_3646755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_3646755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646755 prefixEnd_3646755 := by exact prefixLift 3646755
  have htrace : WordTrace (prefixWord ++ tailWord_3646755) baseStart_3646755 baseEnd_3646755 := by
    simpa [prefixWord, tailWord_3646755, baseEnd_3646755] using wordTrace_append hprefix tailTrace_3646755
  have hstable : (prefixWord ++ tailWord_3646755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646755).length < 2 ^ (prefixWord ++ tailWord_3646755).sum := by decide
  have hdescent : baseEnd_3646755 < baseStart_3646755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646768 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 4]
def baseStart_3646768 : Nat := 118140960795 + 3646768 * 2 ^ 59
def prefixEnd_3646768 : Nat := 4983230072969 + 3 ^ 40 * 3646768 * 2
def baseEnd_3646768 : Nat := 1872544819435493237128825

theorem tailTrace_3646768 : CollatzResearch.WordTrace tailWord_3646768 prefixEnd_3646768 1872544819435493237128825 := by
  unfold tailWord_3646768
  simp only [CollatzResearch.WordTrace]
  refine ⟨66504278026194914617202479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88672370701593219489603305 66504278026194914617202479)
  ·
    refine ⟨99756417039292371925803719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66504278026194914617202479 99756417039292371925803719)
    ·
      refine ⟨149634625558938557888705579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99756417039292371925803719 149634625558938557888705579)
      ·
        refine ⟨224451938338407836833058369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149634625558938557888705579 224451938338407836833058369)
        ·
          refine ⟨168338953753805877624793777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224451938338407836833058369 168338953753805877624793777)
          ·
            refine ⟨126254215315354408218595333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168338953753805877624793777 126254215315354408218595333)
            ·
              refine ⟨23672665371628951540986625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126254215315354408218595333 23672665371628951540986625)
              ·
                refine ⟨17754499028721713655739969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23672665371628951540986625 17754499028721713655739969)
                ·
                  refine ⟨13315874271541285241804977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17754499028721713655739969 13315874271541285241804977)
                  ·
                    refine ⟨9986905703655963931353733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13315874271541285241804977 9986905703655963931353733)
                    ·
                      refine ⟨1872544819435493237128825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9986905703655963931353733 1872544819435493237128825)
                      ·
                        rfl

theorem cell23_3646768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_3646768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646768 prefixEnd_3646768 := by exact prefixLift 3646768
  have htrace : WordTrace (prefixWord ++ tailWord_3646768) baseStart_3646768 baseEnd_3646768 := by
    simpa [prefixWord, tailWord_3646768, baseEnd_3646768] using wordTrace_append hprefix tailTrace_3646768
  have hstable : (prefixWord ++ tailWord_3646768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646768).length < 2 ^ (prefixWord ++ tailWord_3646768).sum := by decide
  have hdescent : baseEnd_3646768 < baseStart_3646768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646772 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_3646772 : Nat := 118140960795 + 3646772 * 2 ^ 59
def prefixEnd_3646772 : Nat := 4983230072969 + 3 ^ 40 * 3646772 * 2
def baseEnd_3646772 : Nat := 1872546873358111221478807

theorem tailTrace_3646772 : CollatzResearch.WordTrace tailWord_3646772 prefixEnd_3646772 1872546873358111221478807 := by
  unfold tailWord_3646772
  simp only [CollatzResearch.WordTrace]
  refine ⟨66504350972187668958775285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88672467962916891945033713 66504350972187668958775285)
  ·
    refine ⟨6234782903642593964885183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66504350972187668958775285 6234782903642593964885183)
    ·
      refine ⟨9352174355463890947327775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6234782903642593964885183 9352174355463890947327775)
      ·
        refine ⟨14028261533195836420991663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9352174355463890947327775 14028261533195836420991663)
        ·
          refine ⟨21042392299793754631487495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14028261533195836420991663 21042392299793754631487495)
          ·
            refine ⟨31563588449690631947231243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21042392299793754631487495 31563588449690631947231243)
            ·
              refine ⟨47345382674535947920846865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31563588449690631947231243 47345382674535947920846865)
              ·
                refine ⟨35509037005901960940635149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47345382674535947920846865 35509037005901960940635149)
                ·
                  refine ⟨13315888877213235352738181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35509037005901960940635149 13315888877213235352738181)
                  ·
                    refine ⟨2496729164477481628638409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13315888877213235352738181 2496729164477481628638409)
                    ·
                      refine ⟨1872546873358111221478807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496729164477481628638409 1872546873358111221478807)
                      ·
                        rfl

theorem cell23_3646772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_3646772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646772 prefixEnd_3646772 := by exact prefixLift 3646772
  have htrace : WordTrace (prefixWord ++ tailWord_3646772) baseStart_3646772 baseEnd_3646772 := by
    simpa [prefixWord, tailWord_3646772, baseEnd_3646772] using wordTrace_append hprefix tailTrace_3646772
  have hstable : (prefixWord ++ tailWord_3646772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646772).length < 2 ^ (prefixWord ++ tailWord_3646772).sum := by decide
  have hdescent : baseEnd_3646772 < baseStart_3646772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646778 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 7]
def baseStart_3646778 : Nat := 118140960795 + 3646778 * 2 ^ 59
def prefixEnd_3646778 : Nat := 4983230072969 + 3 ^ 40 * 3646778 * 2
def baseEnd_3646778 : Nat := 208061106026893133111531

theorem tailTrace_3646778 : CollatzResearch.WordTrace tailWord_3646778 prefixEnd_3646778 208061106026893133111531 := by
  unfold tailWord_3646778
  simp only [CollatzResearch.WordTrace]
  refine ⟨33252230195588400235567247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88672613854902400628179325 33252230195588400235567247)
  ·
    refine ⟨49878345293382600353350871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33252230195588400235567247 49878345293382600353350871)
    ·
      refine ⟨74817517940073900530026307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49878345293382600353350871 74817517940073900530026307)
      ·
        refine ⟨112226276910110850795039461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74817517940073900530026307 112226276910110850795039461)
        ·
          refine ⟨21042426920645784524069899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112226276910110850795039461 21042426920645784524069899)
          ·
            refine ⟨31563640380968676786104849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21042426920645784524069899 31563640380968676786104849)
            ·
              refine ⟨23672730285726507589578637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31563640380968676786104849 23672730285726507589578637)
              ·
                refine ⟨8877273857147440346091989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23672730285726507589578637 8877273857147440346091989)
                ·
                  refine ⟨208061106026893133111531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8877273857147440346091989 208061106026893133111531)
                  ·
                    rfl

theorem cell23_3646778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_3646778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646778 prefixEnd_3646778 := by exact prefixLift 3646778
  have htrace : WordTrace (prefixWord ++ tailWord_3646778) baseStart_3646778 baseEnd_3646778 := by
    simpa [prefixWord, tailWord_3646778, baseEnd_3646778] using wordTrace_append hprefix tailTrace_3646778
  have hstable : (prefixWord ++ tailWord_3646778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646778).length < 2 ^ (prefixWord ++ tailWord_3646778).sum := by decide
  have hdescent : baseEnd_3646778 < baseStart_3646778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646785 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3646785 : Nat := 118140960795 + 3646785 * 2 ^ 59
def prefixEnd_3646785 : Nat := 4983230072969 + 3 ^ 40 * 3646785 * 2
def baseEnd_3646785 : Nat := 1872553548606619670616247

theorem tailTrace_3646785 : CollatzResearch.WordTrace tailWord_3646785 prefixEnd_3646785 1872553548606619670616247 := by
  unfold tailWord_3646785
  simp only [CollatzResearch.WordTrace]
  refine ⟨133009176093328241137773809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88672784062218827425182539 133009176093328241137773809)
  ·
    refine ⟨99756882069996180853330357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133009176093328241137773809 99756882069996180853330357)
    ·
      refine ⟨9352207694062141954999721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99756882069996180853330357 9352207694062141954999721)
      ·
        refine ⟨7014155770546606466249791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9352207694062141954999721 7014155770546606466249791)
        ·
          refine ⟨10521233655819909699374687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7014155770546606466249791 10521233655819909699374687)
          ·
            refine ⟨15781850483729864549062031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10521233655819909699374687 15781850483729864549062031)
            ·
              refine ⟨23672775725594796823593047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15781850483729864549062031 23672775725594796823593047)
              ·
                refine ⟨35509163588392195235389571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23672775725594796823593047 35509163588392195235389571)
                ·
                  refine ⟨53263745382588292853084357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35509163588392195235389571 53263745382588292853084357)
                  ·
                    refine ⟨9986952259235304909953317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53263745382588292853084357 9986952259235304909953317)
                    ·
                      refine ⟨1872553548606619670616247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9986952259235304909953317 1872553548606619670616247)
                      ·
                        rfl

theorem cell23_3646785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3646785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646785 prefixEnd_3646785 := by exact prefixLift 3646785
  have htrace : WordTrace (prefixWord ++ tailWord_3646785) baseStart_3646785 baseEnd_3646785 := by
    simpa [prefixWord, tailWord_3646785, baseEnd_3646785] using wordTrace_append hprefix tailTrace_3646785
  have hstable : (prefixWord ++ tailWord_3646785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646785).length < 2 ^ (prefixWord ++ tailWord_3646785).sum := by decide
  have hdescent : baseEnd_3646785 < baseStart_3646785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646808 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 1, 7]
def baseStart_3646808 : Nat := 118140960795 + 3646808 * 2 ^ 59
def prefixEnd_3646808 : Nat := 4983230072969 + 3 ^ 40 * 3646808 * 2
def baseEnd_3646808 : Nat := 624188452887224360209547

theorem tailTrace_3646808 : CollatzResearch.WordTrace tailWord_3646808 prefixEnd_3646808 624188452887224360209547 := by
  unfold tailWord_3646808
  simp only [CollatzResearch.WordTrace]
  refine ⟨66505007486122458032930539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88673343314829944043907385 66505007486122458032930539)
  ·
    refine ⟨99757511229183687049395809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66505007486122458032930539 99757511229183687049395809)
    ·
      refine ⟨74818133421887765287046857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99757511229183687049395809 74818133421887765287046857)
      ·
        refine ⟨56113600066415823965285143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74818133421887765287046857 56113600066415823965285143)
        ·
          refine ⟨84170400099623735947927715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56113600066415823965285143 84170400099623735947927715)
          ·
            refine ⟨126255600149435603921891573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84170400099623735947927715 126255600149435603921891573)
            ·
              refine ⟨11836462514009587867677335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126255600149435603921891573 11836462514009587867677335)
              ·
                refine ⟨17754693771014381801516003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11836462514009587867677335 17754693771014381801516003)
                ·
                  refine ⟨26632040656521572702274005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17754693771014381801516003 26632040656521572702274005)
                  ·
                    refine ⟨624188452887224360209547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26632040656521572702274005 624188452887224360209547)
                    ·
                      rfl

theorem cell23_3646808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_3646808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646808 prefixEnd_3646808 := by exact prefixLift 3646808
  have htrace : WordTrace (prefixWord ++ tailWord_3646808) baseStart_3646808 baseEnd_3646808 := by
    simpa [prefixWord, tailWord_3646808, baseEnd_3646808] using wordTrace_append hprefix tailTrace_3646808
  have hstable : (prefixWord ++ tailWord_3646808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646808).length < 2 ^ (prefixWord ++ tailWord_3646808).sum := by decide
  have hdescent : baseEnd_3646808 < baseStart_3646808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646823 : List Nat := [1, 1, 5, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_3646823 : Nat := 118140960795 + 3646823 * 2 ^ 59
def prefixEnd_3646823 : Nat := 4983230072969 + 3 ^ 40 * 3646823 * 2
def baseEnd_3646823 : Nat := 1872573060871490521941073

theorem tailTrace_3646823 : CollatzResearch.WordTrace tailWord_3646823 prefixEnd_3646823 1872573060871490521941073 := by
  unfold tailWord_3646823
  simp only [CollatzResearch.WordTrace]
  refine ⟨133010562067190573627657123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88673708044793715751771415 133010562067190573627657123)
  ·
    refine ⟨199515843100785860441485685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133010562067190573627657123 199515843100785860441485685)
    ·
      refine ⟨18704610290698674416389283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199515843100785860441485685 18704610290698674416389283)
      ·
        refine ⟨28056915436048011624583925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18704610290698674416389283 28056915436048011624583925)
        ·
          refine ⟨2630335822129501089804743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28056915436048011624583925 2630335822129501089804743)
          ·
            refine ⟨3945503733194251634707115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630335822129501089804743 3945503733194251634707115)
            ·
              refine ⟨5918255599791377452060673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3945503733194251634707115 5918255599791377452060673)
              ·
                refine ⟨4438691699843533089045505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5918255599791377452060673 4438691699843533089045505)
                ·
                  refine ⟨3329018774882649816784129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4438691699843533089045505 3329018774882649816784129)
                  ·
                    refine ⟨2496764081161987362588097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3329018774882649816784129 2496764081161987362588097)
                    ·
                      refine ⟨1872573060871490521941073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496764081161987362588097 1872573060871490521941073)
                      ·
                        rfl

theorem cell23_3646823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_3646823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646823 prefixEnd_3646823 := by exact prefixLift 3646823
  have htrace : WordTrace (prefixWord ++ tailWord_3646823) baseStart_3646823 baseEnd_3646823 := by
    simpa [prefixWord, tailWord_3646823, baseEnd_3646823] using wordTrace_append hprefix tailTrace_3646823
  have hstable : (prefixWord ++ tailWord_3646823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646823).length < 2 ^ (prefixWord ++ tailWord_3646823).sum := by decide
  have hdescent : baseEnd_3646823 < baseStart_3646823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646882 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_3646882 : Nat := 118140960795 + 3646882 * 2 ^ 59
def prefixEnd_3646882 : Nat := 4983230072969 + 3 ^ 40 * 3646882 * 2
def baseEnd_3646882 : Nat := 1872603356230105791103301

theorem tailTrace_3646882 : CollatzResearch.WordTrace tailWord_3646882 prefixEnd_3646882 1872603356230105791103301 := by
  unfold tailWord_3646882
  simp only [CollatzResearch.WordTrace]
  refine ⟨33253178493494206676013725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88675142649317884469369933 33253178493494206676013725)
  ·
    refine ⟨12469941935060327503505147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33253178493494206676013725 12469941935060327503505147)
    ·
      refine ⟨18704912902590491255257721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12469941935060327503505147 18704912902590491255257721)
      ·
        refine ⟨14028684676942868441443291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18704912902590491255257721 14028684676942868441443291)
        ·
          refine ⟨21043027015414302662164937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14028684676942868441443291 21043027015414302662164937)
          ·
            refine ⟨15782270261560726996623703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21043027015414302662164937 15782270261560726996623703)
            ·
              refine ⟨23673405392341090494935555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15782270261560726996623703 23673405392341090494935555)
              ·
                refine ⟨35510108088511635742403333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23673405392341090494935555 35510108088511635742403333)
                ·
                  refine ⟨6658145266595931701700625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35510108088511635742403333 6658145266595931701700625)
                  ·
                    refine ⟨4993608949946948776275469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6658145266595931701700625 4993608949946948776275469)
                    ·
                      refine ⟨1872603356230105791103301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4993608949946948776275469 1872603356230105791103301)
                      ·
                        rfl

theorem cell23_3646882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_3646882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646882 prefixEnd_3646882 := by exact prefixLift 3646882
  have htrace : WordTrace (prefixWord ++ tailWord_3646882) baseStart_3646882 baseEnd_3646882 := by
    simpa [prefixWord, tailWord_3646882, baseEnd_3646882] using wordTrace_append hprefix tailTrace_3646882
  have hstable : (prefixWord ++ tailWord_3646882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646882).length < 2 ^ (prefixWord ++ tailWord_3646882).sum := by decide
  have hdescent : baseEnd_3646882 < baseStart_3646882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646912 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 3, 1, 3]
def baseStart_3646912 : Nat := 118140960795 + 3646912 * 2 ^ 59
def prefixEnd_3646912 : Nat := 4983230072969 + 3 ^ 40 * 3646912 * 2
def baseEnd_3646912 : Nat := 1872618760649740673728163

theorem tailTrace_3646912 : CollatzResearch.WordTrace tailWord_3646912 prefixEnd_3646912 1872618760649740673728163 := by
  unfold tailWord_3646912
  simp only [CollatzResearch.WordTrace]
  refine ⟨66506904081934070913823495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88675872109245427885097993 66506904081934070913823495)
  ·
    refine ⟨99760356122901106370735243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66506904081934070913823495 99760356122901106370735243)
    ·
      refine ⟨149640534184351659556102865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99760356122901106370735243 149640534184351659556102865)
      ·
        refine ⟨112230400638263744667077149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149640534184351659556102865 112230400638263744667077149)
        ·
          refine ⟨42086400239348904250153931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112230400638263744667077149 42086400239348904250153931)
          ·
            refine ⟨63129600359023356375230897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42086400239348904250153931 63129600359023356375230897)
            ·
              refine ⟨47347200269267517281423173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63129600359023356375230897 47347200269267517281423173)
              ·
                refine ⟨8877600050487659490266845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47347200269267517281423173 8877600050487659490266845)
                ·
                  refine ⟨3329100018932872308850067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8877600050487659490266845 3329100018932872308850067)
                  ·
                    refine ⟨4993650028399308463275101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3329100018932872308850067 4993650028399308463275101)
                    ·
                      refine ⟨1872618760649740673728163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4993650028399308463275101 1872618760649740673728163)
                      ·
                        rfl

theorem cell23_3646912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_3646912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646912 prefixEnd_3646912 := by exact prefixLift 3646912
  have htrace : WordTrace (prefixWord ++ tailWord_3646912) baseStart_3646912 baseEnd_3646912 := by
    simpa [prefixWord, tailWord_3646912, baseEnd_3646912] using wordTrace_append hprefix tailTrace_3646912
  have hstable : (prefixWord ++ tailWord_3646912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646912).length < 2 ^ (prefixWord ++ tailWord_3646912).sum := by decide
  have hdescent : baseEnd_3646912 < baseStart_3646912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646962 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_3646962 : Nat := 118140960795 + 3646962 * 2 ^ 59
def prefixEnd_3646962 : Nat := 4983230072969 + 3 ^ 40 * 3646962 * 2
def baseEnd_3646962 : Nat := 624214811560821826034311

theorem tailTrace_3646962 : CollatzResearch.WordTrace tailWord_3646962 prefixEnd_3646962 624214811560821826034311 := by
  unfold tailWord_3646962
  simp only [CollatzResearch.WordTrace]
  refine ⟨33253907953421750091741785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88677087875791333577978093 33253907953421750091741785)
  ·
    refine ⟨24940430965066312568806339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33253907953421750091741785 24940430965066312568806339)
    ·
      refine ⟨37410646447599468853209509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24940430965066312568806339 37410646447599468853209509)
      ·
        refine ⟨7014496208924900409976783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37410646447599468853209509 7014496208924900409976783)
        ·
          refine ⟨10521744313387350614965175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7014496208924900409976783 10521744313387350614965175)
          ·
            refine ⟨15782616470081025922447763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10521744313387350614965175 15782616470081025922447763)
            ·
              refine ⟨23673924705121538883671645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15782616470081025922447763 23673924705121538883671645)
              ·
                refine ⟨8877721764420577081376867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23673924705121538883671645 8877721764420577081376867)
                ·
                  refine ⟨13316582646630865622065301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8877721764420577081376867 13316582646630865622065301)
                  ·
                    refine ⟨624214811560821826034311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13316582646630865622065301 624214811560821826034311)
                    ·
                      rfl

theorem cell23_3646962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_3646962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646962 prefixEnd_3646962 := by exact prefixLift 3646962
  have htrace : WordTrace (prefixWord ++ tailWord_3646962) baseStart_3646962 baseEnd_3646962 := by
    simpa [prefixWord, tailWord_3646962, baseEnd_3646962] using wordTrace_append hprefix tailTrace_3646962
  have hstable : (prefixWord ++ tailWord_3646962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646962).length < 2 ^ (prefixWord ++ tailWord_3646962).sum := by decide
  have hdescent : baseEnd_3646962 < baseStart_3646962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646972 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_3646972 : Nat := 118140960795 + 3646972 * 2 ^ 59
def prefixEnd_3646972 : Nat := 4983230072969 + 3 ^ 40 * 3646972 * 2
def baseEnd_3646972 : Nat := 1872649569489010438977887

theorem tailTrace_3646972 : CollatzResearch.WordTrace tailWord_3646972 prefixEnd_3646972 1872649569489010438977887 := by
  unfold tailWord_3646972
  simp only [CollatzResearch.WordTrace]
  refine ⟨66507998271825386037415585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88677331029100514716554113 66507998271825386037415585)
  ·
    refine ⟨49880998703869039528061689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66507998271825386037415585 49880998703869039528061689)
    ·
      refine ⟨37410749027901779646046267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49880998703869039528061689 37410749027901779646046267)
      ·
        refine ⟨56116123541852669469069401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37410749027901779646046267 56116123541852669469069401)
        ·
          refine ⟨42087092656389502101802051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56116123541852669469069401 42087092656389502101802051)
          ·
            refine ⟨63130638984584253152703077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42087092656389502101802051 63130638984584253152703077)
            ·
              refine ⟨11836994809609547466131827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63130638984584253152703077 11836994809609547466131827)
              ·
                refine ⟨17755492214414321199197741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11836994809609547466131827 17755492214414321199197741)
                ·
                  refine ⟨6658309580405370449699153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17755492214414321199197741 6658309580405370449699153)
                  ·
                    refine ⟨4993732185304027837274365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6658309580405370449699153 4993732185304027837274365)
                    ·
                      refine ⟨1872649569489010438977887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4993732185304027837274365 1872649569489010438977887)
                      ·
                        rfl

theorem cell23_3646972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_3646972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646972 prefixEnd_3646972 := by exact prefixLift 3646972
  have htrace : WordTrace (prefixWord ++ tailWord_3646972) baseStart_3646972 baseEnd_3646972 := by
    simpa [prefixWord, tailWord_3646972, baseEnd_3646972] using wordTrace_append hprefix tailTrace_3646972
  have hstable : (prefixWord ++ tailWord_3646972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646972).length < 2 ^ (prefixWord ++ tailWord_3646972).sum := by decide
  have hdescent : baseEnd_3646972 < baseStart_3646972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646986 : List Nat := [3, 1, 2, 2, 2, 4, 2, 1, 1, 1, 4]
def baseStart_3646986 : Nat := 118140960795 + 3646986 * 2 ^ 59
def prefixEnd_3646986 : Nat := 4983230072969 + 3 ^ 40 * 3646986 * 2
def baseEnd_3646986 : Nat := 1872656758218173384202823

theorem tailTrace_3646986 : CollatzResearch.WordTrace tailWord_3646986 prefixEnd_3646986 1872656758218173384202823 := by
  unfold tailWord_3646986
  simp only [CollatzResearch.WordTrace]
  refine ⟨33254126791400013116460203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88677671443733368310560541 33254126791400013116460203)
  ·
    refine ⟨49881190187100019674690305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33254126791400013116460203 49881190187100019674690305)
    ·
      refine ⟨37410892640325014756017729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49881190187100019674690305 37410892640325014756017729)
      ·
        refine ⟨28058169480243761067013297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37410892640325014756017729 28058169480243761067013297)
        ·
          refine ⟨21043627110182820800259973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28058169480243761067013297 21043627110182820800259973)
          ·
            refine ⟨3945680083159278900048745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21043627110182820800259973 3945680083159278900048745)
            ·
              refine ⟨2959260062369459175036559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3945680083159278900048745 2959260062369459175036559)
              ·
                refine ⟨4438890093554188762554839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2959260062369459175036559 4438890093554188762554839)
                ·
                  refine ⟨6658335140331283143832259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4438890093554188762554839 6658335140331283143832259)
                  ·
                    refine ⟨9987502710496924715748389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6658335140331283143832259 9987502710496924715748389)
                    ·
                      refine ⟨1872656758218173384202823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9987502710496924715748389 1872656758218173384202823)
                      ·
                        rfl

theorem cell23_3646986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_3646986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646986 prefixEnd_3646986 := by exact prefixLift 3646986
  have htrace : WordTrace (prefixWord ++ tailWord_3646986) baseStart_3646986 baseEnd_3646986 := by
    simpa [prefixWord, tailWord_3646986, baseEnd_3646986] using wordTrace_append hprefix tailTrace_3646986
  have hstable : (prefixWord ++ tailWord_3646986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646986).length < 2 ^ (prefixWord ++ tailWord_3646986).sum := by decide
  have hdescent : baseEnd_3646986 < baseStart_3646986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3646996 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3646996 : Nat := 118140960795 + 3646996 * 2 ^ 59
def prefixEnd_3646996 : Nat := 4983230072969 + 3 ^ 40 * 3646996 * 2
def baseEnd_3646996 : Nat := 624220631008239448359259

theorem tailTrace_3646996 : CollatzResearch.WordTrace tailWord_3646996 prefixEnd_3646996 624220631008239448359259 := by
  unfold tailWord_3646996
  simp only [CollatzResearch.WordTrace]
  refine ⟨66508435947781912086852421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88677914597042549449136561 66508435947781912086852421)
  ·
    refine ⟨12470331740209108516284829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66508435947781912086852421 12470331740209108516284829)
    ·
      refine ⟨4676374402578415693606811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12470331740209108516284829 4676374402578415693606811)
      ·
        refine ⟨7014561603867623540410217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4676374402578415693606811 7014561603867623540410217)
        ·
          refine ⟨5260921202900717655307663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7014561603867623540410217 5260921202900717655307663)
          ·
            refine ⟨7891381804351076482961495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5260921202900717655307663 7891381804351076482961495)
            ·
              refine ⟨11837072706526614724442243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7891381804351076482961495 11837072706526614724442243)
              ·
                refine ⟨17755609059789922086663365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11837072706526614724442243 17755609059789922086663365)
                ·
                  refine ⟨3329176698710610391249381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17755609059789922086663365 3329176698710610391249381)
                  ·
                    refine ⟨624220631008239448359259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3329176698710610391249381 624220631008239448359259)
                    ·
                      rfl

theorem cell23_3646996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3646996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3646996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3646996 prefixEnd_3646996 := by exact prefixLift 3646996
  have htrace : WordTrace (prefixWord ++ tailWord_3646996) baseStart_3646996 baseEnd_3646996 := by
    simpa [prefixWord, tailWord_3646996, baseEnd_3646996] using wordTrace_append hprefix tailTrace_3646996
  have hstable : (prefixWord ++ tailWord_3646996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3646996).length < 2 ^ (prefixWord ++ tailWord_3646996).sum := by decide
  have hdescent : baseEnd_3646996 < baseStart_3646996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3646996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647016 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3647016 : Nat := 118140960795 + 3647016 * 2 ^ 59
def prefixEnd_3647016 : Nat := 4983230072969 + 3 ^ 40 * 3647016 * 2
def baseEnd_3647016 : Nat := 1872672162637808266827685

theorem tailTrace_3647016 : CollatzResearch.WordTrace tailWord_3647016 prefixEnd_3647016 1872672162637808266827685 := by
  unfold tailWord_3647016
  simp only [CollatzResearch.WordTrace]
  refine ⟨66508800677745683794716451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88678400903660911726288601 66508800677745683794716451)
  ·
    refine ⟨99763201016618525692074677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66508800677745683794716451 99763201016618525692074677)
    ·
      refine ⟨9352800095307986783632001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99763201016618525692074677 9352800095307986783632001)
      ·
        refine ⟨7014600071480990087724001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9352800095307986783632001 7014600071480990087724001)
        ·
          refine ⟨5260950053610742565793001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7014600071480990087724001 5260950053610742565793001)
          ·
            refine ⟨3945712540208056924344751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5260950053610742565793001 3945712540208056924344751)
            ·
              refine ⟨5918568810312085386517127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3945712540208056924344751 5918568810312085386517127)
              ·
                refine ⟨8877853215468128079775691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5918568810312085386517127 8877853215468128079775691)
                ·
                  refine ⟨13316779823202192119663537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8877853215468128079775691 13316779823202192119663537)
                  ·
                    refine ⟨9987584867401644089747653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13316779823202192119663537 9987584867401644089747653)
                    ·
                      refine ⟨1872672162637808266827685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9987584867401644089747653 1872672162637808266827685)
                      ·
                        rfl

theorem cell23_3647016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3647016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647016 prefixEnd_3647016 := by exact prefixLift 3647016
  have htrace : WordTrace (prefixWord ++ tailWord_3647016) baseStart_3647016 baseEnd_3647016 := by
    simpa [prefixWord, tailWord_3647016, baseEnd_3647016] using wordTrace_append hprefix tailTrace_3647016
  have hstable : (prefixWord ++ tailWord_3647016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647016).length < 2 ^ (prefixWord ++ tailWord_3647016).sum := by decide
  have hdescent : baseEnd_3647016 < baseStart_3647016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647037 : List Nat := [1, 4, 1, 3, 4, 1, 1, 3, 1, 2, 2]
def baseStart_3647037 : Nat := 118140960795 + 3647037 * 2 ^ 59
def prefixEnd_3647037 : Nat := 4983230072969 + 3 ^ 40 * 3647037 * 2
def baseEnd_3647037 : Nat := 1872682945731552684665089

theorem tailTrace_3647037 : CollatzResearch.WordTrace tailWord_3647037 prefixEnd_3647037 1872682945731552684665089 := by
  unfold tailWord_3647037
  simp only [CollatzResearch.WordTrace]
  refine ⟨133018367288415288175947365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88678911525610192117298243 133018367288415288175947365)
  ·
    refine ⟨24940943866577866532990131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133018367288415288175947365 24940943866577866532990131)
    ·
      refine ⟨37411415799866799799485197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24940943866577866532990131 37411415799866799799485197)
      ·
        refine ⟨14029280924950049924806949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37411415799866799799485197 14029280924950049924806949)
        ·
          refine ⟨2630490173428134360901303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14029280924950049924806949 2630490173428134360901303)
          ·
            refine ⟨3945735260142201541351955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630490173428134360901303 3945735260142201541351955)
            ·
              refine ⟨5918602890213302312027933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3945735260142201541351955 5918602890213302312027933)
              ·
                refine ⟨2219476083829988367010475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5918602890213302312027933 2219476083829988367010475)
                ·
                  refine ⟨3329214125744982550515713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219476083829988367010475 3329214125744982550515713)
                  ·
                    refine ⟨2496910594308736912886785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3329214125744982550515713 2496910594308736912886785)
                    ·
                      refine ⟨1872682945731552684665089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496910594308736912886785 1872682945731552684665089)
                      ·
                        rfl

theorem cell23_3647037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_3647037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647037 prefixEnd_3647037 := by exact prefixLift 3647037
  have htrace : WordTrace (prefixWord ++ tailWord_3647037) baseStart_3647037 baseEnd_3647037 := by
    simpa [prefixWord, tailWord_3647037, baseEnd_3647037] using wordTrace_append hprefix tailTrace_3647037
  have hstable : (prefixWord ++ tailWord_3647037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647037).length < 2 ^ (prefixWord ++ tailWord_3647037).sum := by decide
  have hdescent : baseEnd_3647037 < baseStart_3647037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647149 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_3647149 : Nat := 118140960795 + 3647149 * 2 ^ 59
def prefixEnd_3647149 : Nat := 4983230072969 + 3 ^ 40 * 3647149 * 2
def baseEnd_3647149 : Nat := 1872740455564856246464573

theorem tailTrace_3647149 : CollatzResearch.WordTrace tailWord_3647149 prefixEnd_3647149 1872740455564856246464573 := by
  unfold tailWord_3647149
  simp only [CollatzResearch.WordTrace]
  refine ⟨133022452264009531304024501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88681634842673020869349667 133022452264009531304024501)
  ·
    refine ⟨12470854899750893559752297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133022452264009531304024501 12470854899750893559752297)
    ·
      refine ⟨9353141174813170169814223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12470854899750893559752297 9353141174813170169814223)
      ·
        refine ⟨14029711762219755254721335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9353141174813170169814223 14029711762219755254721335)
        ·
          refine ⟨21044567643329632882082003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14029711762219755254721335 21044567643329632882082003)
          ·
            refine ⟨31566851464994449323123005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21044567643329632882082003 31566851464994449323123005)
            ·
              refine ⟨11837569299372918496171127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31566851464994449323123005 11837569299372918496171127)
              ·
                refine ⟨17756353949059377744256691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11837569299372918496171127 17756353949059377744256691)
                ·
                  refine ⟨26634530923589066616385037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17756353949059377744256691 26634530923589066616385037)
                  ·
                    refine ⟨9987949096345899981144389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26634530923589066616385037 9987949096345899981144389)
                    ·
                      refine ⟨1872740455564856246464573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9987949096345899981144389 1872740455564856246464573)
                      ·
                        rfl

theorem cell23_3647149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_3647149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647149 prefixEnd_3647149 := by exact prefixLift 3647149
  have htrace : WordTrace (prefixWord ++ tailWord_3647149) baseStart_3647149 baseEnd_3647149 := by
    simpa [prefixWord, tailWord_3647149, baseEnd_3647149] using wordTrace_append hprefix tailTrace_3647149
  have hstable : (prefixWord ++ tailWord_3647149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647149).length < 2 ^ (prefixWord ++ tailWord_3647149).sum := by decide
  have hdescent : baseEnd_3647149 < baseStart_3647149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647162 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_3647162 : Nat := 118140960795 + 3647162 * 2 ^ 59
def prefixEnd_3647162 : Nat := 4983230072969 + 3 ^ 40 * 3647162 * 2
def baseEnd_3647162 : Nat := 1872747130813364695602013

theorem tailTrace_3647162 : CollatzResearch.WordTrace tailWord_3647162 prefixEnd_3647162 1872747130813364695602013 := by
  unfold tailWord_3647162
  simp only [CollatzResearch.WordTrace]
  refine ⟨33255731603240608631061935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88681950941974956349498493 33255731603240608631061935)
  ·
    refine ⟨49883597404860912946592903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33255731603240608631061935 49883597404860912946592903)
    ·
      refine ⟨74825396107291369419889355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49883597404860912946592903 74825396107291369419889355)
      ·
        refine ⟨112238094160937054129834033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74825396107291369419889355 112238094160937054129834033)
        ·
          refine ⟨84178570620702790597375525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112238094160937054129834033 84178570620702790597375525)
          ·
            refine ⟨15783481991381773237007911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84178570620702790597375525 15783481991381773237007911)
            ·
              refine ⟨23675222987072659855511867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15783481991381773237007911 23675222987072659855511867)
              ·
                refine ⟨35512834480608989783267801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23675222987072659855511867 35512834480608989783267801)
                ·
                  refine ⟨26634625860456742337450851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35512834480608989783267801 26634625860456742337450851)
                  ·
                    refine ⟨39951938790685113506176277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26634625860456742337450851 39951938790685113506176277)
                    ·
                      refine ⟨1872747130813364695602013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39951938790685113506176277 1872747130813364695602013)
                      ·
                        rfl

theorem cell23_3647162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_3647162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647162 prefixEnd_3647162 := by exact prefixLift 3647162
  have htrace : WordTrace (prefixWord ++ tailWord_3647162) baseStart_3647162 baseEnd_3647162 := by
    simpa [prefixWord, tailWord_3647162, baseEnd_3647162] using wordTrace_append hprefix tailTrace_3647162
  have hstable : (prefixWord ++ tailWord_3647162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647162).length < 2 ^ (prefixWord ++ tailWord_3647162).sum := by decide
  have hdescent : baseEnd_3647162 < baseStart_3647162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647166 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_3647166 : Nat := 118140960795 + 3647166 * 2 ^ 59
def prefixEnd_3647166 : Nat := 4983230072969 + 3 ^ 40 * 3647166 * 2
def baseEnd_3647166 : Nat := 1872749184735982679951995

theorem tailTrace_3647166 : CollatzResearch.WordTrace tailWord_3647166 prefixEnd_3647166 1872749184735982679951995 := by
  unfold tailWord_3647166
  simp only [CollatzResearch.WordTrace]
  refine ⟨16627884038118492900924169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88682048203298628804928901 16627884038118492900924169)
  ·
    refine ⟨12470913028588869675693127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16627884038118492900924169 12470913028588869675693127)
    ·
      refine ⟨18706369542883304513539691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12470913028588869675693127 18706369542883304513539691)
      ·
        refine ⟨28059554314324956770309537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18706369542883304513539691 28059554314324956770309537)
        ·
          refine ⟨21044665735743717577732153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28059554314324956770309537 21044665735743717577732153)
          ·
            refine ⟨15783499301807788183299115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21044665735743717577732153 15783499301807788183299115)
            ·
              refine ⟨23675248952711682274948673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15783499301807788183299115 23675248952711682274948673)
              ·
                refine ⟨17756436714533761706211505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23675248952711682274948673 17756436714533761706211505)
                ·
                  refine ⟨13317327535900321279658629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17756436714533761706211505 13317327535900321279658629)
                  ·
                    refine ⟨2496998912981310239935993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13317327535900321279658629 2496998912981310239935993)
                    ·
                      refine ⟨1872749184735982679951995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2496998912981310239935993 1872749184735982679951995)
                      ·
                        rfl

theorem cell23_3647166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_3647166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647166 prefixEnd_3647166 := by exact prefixLift 3647166
  have htrace : WordTrace (prefixWord ++ tailWord_3647166) baseStart_3647166 baseEnd_3647166 := by
    simpa [prefixWord, tailWord_3647166, baseEnd_3647166] using wordTrace_append hprefix tailTrace_3647166
  have hstable : (prefixWord ++ tailWord_3647166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647166).length < 2 ^ (prefixWord ++ tailWord_3647166).sum := by decide
  have hdescent : baseEnd_3647166 < baseStart_3647166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647176 : List Nat := [2, 1, 3, 1, 2, 2, 1, 6, 1, 4]
def baseStart_3647176 : Nat := 118140960795 + 3647176 * 2 ^ 59
def prefixEnd_3647176 : Nat := 4983230072969 + 3 ^ 40 * 3647176 * 2
def baseEnd_3647176 : Nat := 624251439847509213608983

theorem tailTrace_3647176 : CollatzResearch.WordTrace tailWord_3647176 prefixEnd_3647176 624251439847509213608983 := by
  unfold tailWord_3647176
  simp only [CollatzResearch.WordTrace]
  refine ⟨66511718517455857457628691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88682291356607809943504921 66511718517455857457628691)
  ·
    refine ⟨99767577776183786186443037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66511718517455857457628691 99767577776183786186443037)
    ·
      refine ⟨37412841666068919819916139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99767577776183786186443037 37412841666068919819916139)
      ·
        refine ⟨56119262499103379729874209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37412841666068919819916139 56119262499103379729874209)
        ·
          refine ⟨42089446874327534797405657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56119262499103379729874209 42089446874327534797405657)
          ·
            refine ⟨31567085155745651098054243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42089446874327534797405657 31567085155745651098054243)
            ·
              refine ⟨47350627733618476647081365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31567085155745651098054243 47350627733618476647081365)
              ·
                refine ⟨2219560675013366092831939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47350627733618476647081365 2219560675013366092831939)
                ·
                  refine ⟨3329341012520049139247909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219560675013366092831939 3329341012520049139247909)
                  ·
                    refine ⟨624251439847509213608983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3329341012520049139247909 624251439847509213608983)
                    ·
                      rfl

theorem cell23_3647176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_3647176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647176 prefixEnd_3647176 := by exact prefixLift 3647176
  have htrace : WordTrace (prefixWord ++ tailWord_3647176) baseStart_3647176 baseEnd_3647176 := by
    simpa [prefixWord, tailWord_3647176, baseEnd_3647176] using wordTrace_append hprefix tailTrace_3647176
  have hstable : (prefixWord ++ tailWord_3647176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647176).length < 2 ^ (prefixWord ++ tailWord_3647176).sum := by decide
  have hdescent : baseEnd_3647176 < baseStart_3647176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647192 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_3647192 : Nat := 118140960795 + 3647192 * 2 ^ 59
def prefixEnd_3647192 : Nat := 4983230072969 + 3 ^ 40 * 3647192 * 2
def baseEnd_3647192 : Nat := 1872762535232999578226875

theorem tailTrace_3647192 : CollatzResearch.WordTrace tailWord_3647192 prefixEnd_3647192 1872762535232999578226875 := by
  unfold tailWord_3647192
  simp only [CollatzResearch.WordTrace]
  refine ⟨66512010301426874823919915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88682680401902499765226553 66512010301426874823919915)
  ·
    refine ⟨99768015452140312235879873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66512010301426874823919915 99768015452140312235879873)
    ·
      refine ⟨74826011589105234176909905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99768015452140312235879873 74826011589105234176909905)
      ·
        refine ⟨56119508691828925632682429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74826011589105234176909905 56119508691828925632682429)
        ·
          refine ⟨21044815759435847112255911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56119508691828925632682429 21044815759435847112255911)
          ·
            refine ⟨31567223639153770668383867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21044815759435847112255911 31567223639153770668383867)
            ·
              refine ⟨47350835458730656002575801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31567223639153770668383867 47350835458730656002575801)
              ·
                refine ⟨35513126594047992001931851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47350835458730656002575801 35513126594047992001931851)
                ·
                  refine ⟨53269689891071988002897777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35513126594047992001931851 53269689891071988002897777)
                  ·
                    refine ⟨39952267418303991002173333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53269689891071988002897777 39952267418303991002173333)
                    ·
                      refine ⟨1872762535232999578226875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39952267418303991002173333 1872762535232999578226875)
                      ·
                        rfl

theorem cell23_3647192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_3647192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647192 prefixEnd_3647192 := by exact prefixLift 3647192
  have htrace : WordTrace (prefixWord ++ tailWord_3647192) baseStart_3647192 baseEnd_3647192 := by
    simpa [prefixWord, tailWord_3647192, baseEnd_3647192] using wordTrace_append hprefix tailTrace_3647192
  have hstable : (prefixWord ++ tailWord_3647192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647192).length < 2 ^ (prefixWord ++ tailWord_3647192).sum := by decide
  have hdescent : baseEnd_3647192 < baseStart_3647192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647219 : List Nat := [1, 1, 1, 2, 2, 3, 4, 3, 1, 5]
def baseStart_3647219 : Nat := 118140960795 + 3647219 * 2 ^ 59
def prefixEnd_3647219 : Nat := 4983230072969 + 3 ^ 40 * 3647219 * 2
def baseEnd_3647219 : Nat := 624258799736890324196417

theorem tailTrace_3647219 : CollatzResearch.WordTrace tailWord_3647219 prefixEnd_3647219 624258799736890324196417 := by
  unfold tailWord_3647219
  simp only [CollatzResearch.WordTrace]
  refine ⟨133025005373755933259072711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88683336915837288839381807 133025005373755933259072711)
  ·
    refine ⟨199537508060633899888609067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133025005373755933259072711 199537508060633899888609067)
    ·
      refine ⟨299306262090950849832913601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199537508060633899888609067 299306262090950849832913601)
      ·
        refine ⟨224479696568213137374685201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299306262090950849832913601 224479696568213137374685201)
        ·
          refine ⟨168359772426159853031013901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224479696568213137374685201 168359772426159853031013901)
          ·
            refine ⟨63134914659809944886630213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168359772426159853031013901 63134914659809944886630213)
            ·
              refine ⟨11837796498714364666243165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63134914659809944886630213 11837796498714364666243165)
              ·
                refine ⟨4439173687017886749841187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11837796498714364666243165 4439173687017886749841187)
                ·
                  refine ⟨6658760530526830124761781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4439173687017886749841187 6658760530526830124761781)
                  ·
                    refine ⟨624258799736890324196417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6658760530526830124761781 624258799736890324196417)
                    ·
                      rfl

theorem cell23_3647219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 5].length) (baseStart_3647219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647219 prefixEnd_3647219 := by exact prefixLift 3647219
  have htrace : WordTrace (prefixWord ++ tailWord_3647219) baseStart_3647219 baseEnd_3647219 := by
    simpa [prefixWord, tailWord_3647219, baseEnd_3647219] using wordTrace_append hprefix tailTrace_3647219
  have hstable : (prefixWord ++ tailWord_3647219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647219).length < 2 ^ (prefixWord ++ tailWord_3647219).sum := by decide
  have hdescent : baseEnd_3647219 < baseStart_3647219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647220 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3647220 : Nat := 118140960795 + 3647220 * 2 ^ 59
def prefixEnd_3647220 : Nat := 4983230072969 + 3 ^ 40 * 3647220 * 2
def baseEnd_3647220 : Nat := 1872776912691325468676747

theorem tailTrace_3647220 : CollatzResearch.WordTrace tailWord_3647220 prefixEnd_3647220 1872776912691325468676747 := by
  unfold tailWord_3647220
  simp only [CollatzResearch.WordTrace]
  refine ⟨66512520923376155214929557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88683361231168206953239409 66512520923376155214929557)
  ·
    refine ⟨3117774418283257275699823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66512520923376155214929557 3117774418283257275699823)
    ·
      refine ⟨4676661627424885913549735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3117774418283257275699823 4676661627424885913549735)
      ·
        refine ⟨7014992441137328870324603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4676661627424885913549735 7014992441137328870324603)
        ·
          refine ⟨10522488661705993305486905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7014992441137328870324603 10522488661705993305486905)
          ·
            refine ⟨7891866496279494979115179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10522488661705993305486905 7891866496279494979115179)
            ·
              refine ⟨11837799744419242468672769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7891866496279494979115179 11837799744419242468672769)
              ·
                refine ⟨8878349808314431851504577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11837799744419242468672769 8878349808314431851504577)
                ·
                  refine ⟨6658762356235823888628433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8878349808314431851504577 6658762356235823888628433)
                  ·
                    refine ⟨4994071767176867916471325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6658762356235823888628433 4994071767176867916471325)
                    ·
                      refine ⟨1872776912691325468676747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4994071767176867916471325 1872776912691325468676747)
                      ·
                        rfl

theorem cell23_3647220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3647220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647220 prefixEnd_3647220 := by exact prefixLift 3647220
  have htrace : WordTrace (prefixWord ++ tailWord_3647220) baseStart_3647220 baseEnd_3647220 := by
    simpa [prefixWord, tailWord_3647220, baseEnd_3647220] using wordTrace_append hprefix tailTrace_3647220
  have hstable : (prefixWord ++ tailWord_3647220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647220).length < 2 ^ (prefixWord ++ tailWord_3647220).sum := by decide
  have hdescent : baseEnd_3647220 < baseStart_3647220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647232 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 3, 6]
def baseStart_3647232 : Nat := 118140960795 + 3647232 * 2 ^ 59
def prefixEnd_3647232 : Nat := 4983230072969 + 3 ^ 40 * 3647232 * 2
def baseEnd_3647232 : Nat := 624261024819726473908897

theorem tailTrace_3647232 : CollatzResearch.WordTrace tailWord_3647232 prefixEnd_3647232 624261024819726473908897 := by
  unfold tailWord_3647232
  simp only [CollatzResearch.WordTrace]
  refine ⟨66512739761354418239647975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88683653015139224319530633 66512739761354418239647975)
  ·
    refine ⟨99769109642031627359471963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66512739761354418239647975 99769109642031627359471963)
    ·
      refine ⟨149653664463047441039207945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99769109642031627359471963 149653664463047441039207945)
      ·
        refine ⟨112240248347285580779405959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149653664463047441039207945 112240248347285580779405959)
        ·
          refine ⟨168360372520928371169108939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112240248347285580779405959 168360372520928371169108939)
          ·
            refine ⟨252540558781392556753663409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168360372520928371169108939 252540558781392556753663409)
            ·
              refine ⟨189405419086044417565247557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252540558781392556753663409 189405419086044417565247557)
              ·
                refine ⟨35513516078633328293483917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189405419086044417565247557 35513516078633328293483917)
                ·
                  refine ⟨13317568529487498110056469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35513516078633328293483917 13317568529487498110056469)
                  ·
                    refine ⟨624261024819726473908897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13317568529487498110056469 624261024819726473908897)
                    ·
                      rfl

theorem cell23_3647232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 6].length) (baseStart_3647232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647232 prefixEnd_3647232 := by exact prefixLift 3647232
  have htrace : WordTrace (prefixWord ++ tailWord_3647232) baseStart_3647232 baseEnd_3647232 := by
    simpa [prefixWord, tailWord_3647232, baseEnd_3647232] using wordTrace_append hprefix tailTrace_3647232
  have hstable : (prefixWord ++ tailWord_3647232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647232).length < 2 ^ (prefixWord ++ tailWord_3647232).sum := by decide
  have hdescent : baseEnd_3647232 < baseStart_3647232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647233 : List Nat := [1, 2, 4, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_3647233 : Nat := 118140960795 + 3647233 * 2 ^ 59
def prefixEnd_3647233 : Nat := 4983230072969 + 3 ^ 40 * 3647233 * 2
def baseEnd_3647233 : Nat := 1872783587939833917814187

theorem tailTrace_3647233 : CollatzResearch.WordTrace tailWord_3647233 prefixEnd_3647233 1872783587939833917814187 := by
  unfold tailWord_3647233
  simp only [CollatzResearch.WordTrace]
  refine ⟨133025515995705213650082353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88683677330470142433388235 133025515995705213650082353)
  ·
    refine ⟨99769136996778910237561765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133025515995705213650082353 99769136996778910237561765)
    ·
      refine ⟨18706713186896045669542831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99769136996778910237561765 18706713186896045669542831)
      ·
        refine ⟨28060069780344068504314247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18706713186896045669542831 28060069780344068504314247)
        ·
          refine ⟨42090104670516102756471371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28060069780344068504314247 42090104670516102756471371)
          ·
            refine ⟨63135157005774154134707057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42090104670516102756471371 63135157005774154134707057)
            ·
              refine ⟨47351367754330615601030293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63135157005774154134707057 47351367754330615601030293)
              ·
                refine ⟨2219595363484247606298295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47351367754330615601030293 2219595363484247606298295)
                ·
                  refine ⟨3329393045226371409447443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219595363484247606298295 3329393045226371409447443)
                  ·
                    refine ⟨4994089567839557114171165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3329393045226371409447443 4994089567839557114171165)
                    ·
                      refine ⟨1872783587939833917814187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4994089567839557114171165 1872783587939833917814187)
                      ·
                        rfl

theorem cell23_3647233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_3647233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647233 prefixEnd_3647233 := by exact prefixLift 3647233
  have htrace : WordTrace (prefixWord ++ tailWord_3647233) baseStart_3647233 baseEnd_3647233 := by
    simpa [prefixWord, tailWord_3647233, baseEnd_3647233] using wordTrace_append hprefix tailTrace_3647233
  have hstable : (prefixWord ++ tailWord_3647233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647233).length < 2 ^ (prefixWord ++ tailWord_3647233).sum := by decide
  have hdescent : baseEnd_3647233 < baseStart_3647233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647256 : List Nat := [2, 1, 2, 3, 1, 1, 5, 2, 1, 1, 4]
def baseStart_3647256 : Nat := 118140960795 + 3647256 * 2 ^ 59
def prefixEnd_3647256 : Nat := 4983230072969 + 3 ^ 40 * 3647256 * 2
def baseEnd_3647256 : Nat := 1872795397994887327826581

theorem tailTrace_3647256 : CollatzResearch.WordTrace tailWord_3647256 prefixEnd_3647256 1872795397994887327826581 := by
  unfold tailWord_3647256
  simp only [CollatzResearch.WordTrace]
  refine ⟨66513177437310944289084811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88684236583081259052113081 66513177437310944289084811)
  ·
    refine ⟨99769766155966416433627217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66513177437310944289084811 99769766155966416433627217)
    ·
      refine ⟨74827324616974812325220413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99769766155966416433627217 74827324616974812325220413)
      ·
        refine ⟨28060246731365554621957655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74827324616974812325220413 28060246731365554621957655)
        ·
          refine ⟨42090370097048331932936483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28060246731365554621957655 42090370097048331932936483)
          ·
            refine ⟨63135555145572497899404725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42090370097048331932936483 63135555145572497899404725)
            ·
              refine ⟨5918958294897421678069193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63135555145572497899404725 5918958294897421678069193)
              ·
                refine ⟨4439218721173066258551895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5918958294897421678069193 4439218721173066258551895)
                ·
                  refine ⟨6658828081759599387827843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4439218721173066258551895 6658828081759599387827843)
                  ·
                    refine ⟨9988242122639399081741765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6658828081759599387827843 9988242122639399081741765)
                    ·
                      refine ⟨1872795397994887327826581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9988242122639399081741765 1872795397994887327826581)
                      ·
                        rfl

theorem cell23_3647256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_3647256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647256 prefixEnd_3647256 := by exact prefixLift 3647256
  have htrace : WordTrace (prefixWord ++ tailWord_3647256) baseStart_3647256 baseEnd_3647256 := by
    simpa [prefixWord, tailWord_3647256, baseEnd_3647256] using wordTrace_append hprefix tailTrace_3647256
  have hstable : (prefixWord ++ tailWord_3647256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647256).length < 2 ^ (prefixWord ++ tailWord_3647256).sum := by decide
  have hdescent : baseEnd_3647256 < baseStart_3647256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647259 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 3]
def baseStart_3647259 : Nat := 118140960795 + 3647259 * 2 ^ 59
def prefixEnd_3647259 : Nat := 4983230072969 + 3 ^ 40 * 3647259 * 2
def baseEnd_3647259 : Nat := 1872796938436850816089067

theorem tailTrace_3647259 : CollatzResearch.WordTrace tailWord_3647259 prefixEnd_3647259 1872796938436850816089067 := by
  unfold tailWord_3647259
  simp only [CollatzResearch.WordTrace]
  refine ⟨133026464293611020090528831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88684309529074013393685887 133026464293611020090528831)
  ·
    refine ⟨199539696440416530135793247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133026464293611020090528831 199539696440416530135793247)
    ·
      refine ⟨299309544660624795203689871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199539696440416530135793247 299309544660624795203689871)
      ·
        refine ⟨448964316990937192805534807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299309544660624795203689871 448964316990937192805534807)
        ·
          refine ⟨673446475486405789208302211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448964316990937192805534807 673446475486405789208302211)
          ·
            refine ⟨1010169713229608683812453317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673446475486405789208302211 1010169713229608683812453317)
            ·
              refine ⟨189406821230551628214834997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1010169713229608683812453317 189406821230551628214834997)
              ·
                refine ⟨17756889490364215145140781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189406821230551628214834997 17756889490364215145140781)
                ·
                  refine ⟨6658833558886580679427793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17756889490364215145140781 6658833558886580679427793)
                  ·
                    refine ⟨4994125169164935509570845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6658833558886580679427793 4994125169164935509570845)
                    ·
                      refine ⟨1872796938436850816089067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4994125169164935509570845 1872796938436850816089067)
                      ·
                        rfl

theorem cell23_3647259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 3].length) (baseStart_3647259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647259 prefixEnd_3647259 := by exact prefixLift 3647259
  have htrace : WordTrace (prefixWord ++ tailWord_3647259) baseStart_3647259 baseEnd_3647259 := by
    simpa [prefixWord, tailWord_3647259, baseEnd_3647259] using wordTrace_append hprefix tailTrace_3647259
  have hstable : (prefixWord ++ tailWord_3647259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647259).length < 2 ^ (prefixWord ++ tailWord_3647259).sum := by decide
  have hdescent : baseEnd_3647259 < baseStart_3647259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647269 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_3647269 : Nat := 118140960795 + 3647269 * 2 ^ 59
def prefixEnd_3647269 : Nat := 4983230072969 + 3 ^ 40 * 3647269 * 2
def baseEnd_3647269 : Nat := 1872802073243395776964021

theorem tailTrace_3647269 : CollatzResearch.WordTrace tailWord_3647269 prefixEnd_3647269 1872802073243395776964021 := by
  unfold tailWord_3647269
  simp only [CollatzResearch.WordTrace]
  refine ⟨133026829023574791798392861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88684552682383194532261907 133026829023574791798392861)
  ·
    refine ⟨49885060883840546924397323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133026829023574791798392861 49885060883840546924397323)
    ·
      refine ⟨74827591325760820386595985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49885060883840546924397323 74827591325760820386595985)
      ·
        refine ⟨56120693494320615289946989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74827591325760820386595985 56120693494320615289946989)
        ·
          refine ⟨21045260060370230733730121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56120693494320615289946989 21045260060370230733730121)
          ·
            refine ⟨15783945045277673050297591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21045260060370230733730121 15783945045277673050297591)
            ·
              refine ⟨23675917567916509575446387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15783945045277673050297591 23675917567916509575446387)
              ·
                refine ⟨35513876351874764363169581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23675917567916509575446387 35513876351874764363169581)
                ·
                  refine ⟨13317703631953036636188593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35513876351874764363169581 13317703631953036636188593)
                  ·
                    refine ⟨9988277723964777477141445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13317703631953036636188593 9988277723964777477141445)
                    ·
                      refine ⟨1872802073243395776964021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9988277723964777477141445 1872802073243395776964021)
                      ·
                        rfl

theorem cell23_3647269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_3647269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647269 prefixEnd_3647269 := by exact prefixLift 3647269
  have htrace : WordTrace (prefixWord ++ tailWord_3647269) baseStart_3647269 baseEnd_3647269 := by
    simpa [prefixWord, tailWord_3647269, baseEnd_3647269] using wordTrace_append hprefix tailTrace_3647269
  have hstable : (prefixWord ++ tailWord_3647269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647269).length < 2 ^ (prefixWord ++ tailWord_3647269).sum := by decide
  have hdescent : baseEnd_3647269 < baseStart_3647269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647276 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 5]
def baseStart_3647276 : Nat := 118140960795 + 3647276 * 2 ^ 59
def prefixEnd_3647276 : Nat := 4983230072969 + 3 ^ 40 * 3647276 * 2
def baseEnd_3647276 : Nat := 1872805667607977249576489

theorem tailTrace_3647276 : CollatzResearch.WordTrace tailWord_3647276 prefixEnd_3647276 1872805667607977249576489 := by
  unfold tailWord_3647276
  simp only [CollatzResearch.WordTrace]
  refine ⟨66513542167274715996948841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88684722889699621329265121 66513542167274715996948841)
  ·
    refine ⟨49885156625456036997711631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66513542167274715996948841 49885156625456036997711631)
    ·
      refine ⟨74827734938184055496567447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49885156625456036997711631 74827734938184055496567447)
      ·
        refine ⟨112241602407276083244851171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74827734938184055496567447 112241602407276083244851171)
        ·
          refine ⟨168362403610914124867276757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112241602407276083244851171 168362403610914124867276757)
          ·
            refine ⟨3945993834630799801576799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 168362403610914124867276757 3945993834630799801576799)
            ·
              refine ⟨5918990751946199702365199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3945993834630799801576799 5918990751946199702365199)
              ·
                refine ⟨8878486127919299553547799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5918990751946199702365199 8878486127919299553547799)
                ·
                  refine ⟨13317729191878949330321699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8878486127919299553547799 13317729191878949330321699)
                  ·
                    refine ⟨19976593787818423995482549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13317729191878949330321699 19976593787818423995482549)
                    ·
                      refine ⟨1872805667607977249576489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19976593787818423995482549 1872805667607977249576489)
                      ·
                        rfl

theorem cell23_3647276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 5].length) (baseStart_3647276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647276 prefixEnd_3647276 := by exact prefixLift 3647276
  have htrace : WordTrace (prefixWord ++ tailWord_3647276) baseStart_3647276 baseEnd_3647276 := by
    simpa [prefixWord, tailWord_3647276, baseEnd_3647276] using wordTrace_append hprefix tailTrace_3647276
  have hstable : (prefixWord ++ tailWord_3647276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647276).length < 2 ^ (prefixWord ++ tailWord_3647276).sum := by decide
  have hdescent : baseEnd_3647276 < baseStart_3647276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647283 : List Nat := [1, 1, 1, 2, 7, 1, 2, 2, 2, 4]
def baseStart_3647283 : Nat := 118140960795 + 3647283 * 2 ^ 59
def prefixEnd_3647283 : Nat := 4983230072969 + 3 ^ 40 * 3647283 * 2
def baseEnd_3647283 : Nat := 624269753990852907396319

theorem tailTrace_3647283 : CollatzResearch.WordTrace tailWord_3647283 prefixEnd_3647283 624269753990852907396319 := by
  unfold tailWord_3647283
  simp only [CollatzResearch.WordTrace]
  refine ⟨133027339645524072189402503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88684893097016048126268335 133027339645524072189402503)
  ·
    refine ⟨199541009468286108284103755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133027339645524072189402503 199541009468286108284103755)
    ·
      refine ⟨299311514202429162426155633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199541009468286108284103755 299311514202429162426155633)
      ·
        refine ⟨224483635651821871819616725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299311514202429162426155633 224483635651821871819616725)
        ·
          refine ⟨5261335210589575120772267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 224483635651821871819616725 5261335210589575120772267)
          ·
            refine ⟨7892002815884362681158401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5261335210589575120772267 7892002815884362681158401)
            ·
              refine ⟨5919002111913272010868801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7892002815884362681158401 5919002111913272010868801)
              ·
                refine ⟨4439251583934954008151601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5919002111913272010868801 4439251583934954008151601)
                ·
                  refine ⟨3329438687951215506113701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4439251583934954008151601 3329438687951215506113701)
                  ·
                    refine ⟨624269753990852907396319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3329438687951215506113701 624269753990852907396319)
                    ·
                      rfl

theorem cell23_3647283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 4].length) (baseStart_3647283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647283 prefixEnd_3647283 := by exact prefixLift 3647283
  have htrace : WordTrace (prefixWord ++ tailWord_3647283) baseStart_3647283 baseEnd_3647283 := by
    simpa [prefixWord, tailWord_3647283, baseEnd_3647283] using wordTrace_append hprefix tailTrace_3647283
  have hstable : (prefixWord ++ tailWord_3647283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647283).length < 2 ^ (prefixWord ++ tailWord_3647283).sum := by decide
  have hdescent : baseEnd_3647283 < baseStart_3647283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647284 : List Nat := [2, 5, 1, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_3647284 : Nat := 118140960795 + 3647284 * 2 ^ 59
def prefixEnd_3647284 : Nat := 4983230072969 + 3 ^ 40 * 3647284 * 2
def baseEnd_3647284 : Nat := 1872809775453213218276453

theorem tailTrace_3647284 : CollatzResearch.WordTrace tailWord_3647284 prefixEnd_3647284 1872809775453213218276453 := by
  unfold tailWord_3647284
  simp only [CollatzResearch.WordTrace]
  refine ⟨66513688059260224680094453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88684917412346966240125937 66513688059260224680094453)
  ·
    refine ⟨6235658255555646063758855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66513688059260224680094453 6235658255555646063758855)
    ·
      refine ⟨9353487383333469095638283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6235658255555646063758855 9353487383333469095638283)
      ·
        refine ⟨14030231075000203643457425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9353487383333469095638283 14030231075000203643457425)
        ·
          refine ⟨10522673306250152732593069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14030231075000203643457425 10522673306250152732593069)
          ·
            refine ⟨3946002489843807274722401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10522673306250152732593069 3946002489843807274722401)
            ·
              refine ⟨2959501867382855456041801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3946002489843807274722401 2959501867382855456041801)
              ·
                refine ⟨2219626400537141592031351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2959501867382855456041801 2219626400537141592031351)
                ·
                  refine ⟨3329439600805712388047027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219626400537141592031351 3329439600805712388047027)
                  ·
                    refine ⟨4994159401208568582070541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3329439600805712388047027 4994159401208568582070541)
                    ·
                      refine ⟨1872809775453213218276453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4994159401208568582070541 1872809775453213218276453)
                      ·
                        rfl

theorem cell23_3647284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_3647284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647284 prefixEnd_3647284 := by exact prefixLift 3647284
  have htrace : WordTrace (prefixWord ++ tailWord_3647284) baseStart_3647284 baseEnd_3647284 := by
    simpa [prefixWord, tailWord_3647284, baseEnd_3647284] using wordTrace_append hprefix tailTrace_3647284
  have hstable : (prefixWord ++ tailWord_3647284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647284).length < 2 ^ (prefixWord ++ tailWord_3647284).sum := by decide
  have hdescent : baseEnd_3647284 < baseStart_3647284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647306 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_3647306 : Nat := 118140960795 + 3647306 * 2 ^ 59
def prefixEnd_3647306 : Nat := 4983230072969 + 3 ^ 40 * 3647306 * 2
def baseEnd_3647306 : Nat := 1872821072027612132201351

theorem tailTrace_3647306 : CollatzResearch.WordTrace tailWord_3647306 prefixEnd_3647306 1872821072027612132201351 := by
  unfold tailWord_3647306
  simp only [CollatzResearch.WordTrace]
  refine ⟨33257044631110186779372443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88685452349627164744993181 33257044631110186779372443)
  ·
    refine ⟨49885566946665280169058665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33257044631110186779372443 49885566946665280169058665)
    ·
      refine ⟨37414175209998960126793999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49885566946665280169058665 37414175209998960126793999)
      ·
        refine ⟨56121262814998440190190999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37414175209998960126793999 56121262814998440190190999)
        ·
          refine ⟨84181894222497660285286499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56121262814998440190190999 84181894222497660285286499)
          ·
            refine ⟨126272841333746490427929749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84181894222497660285286499 126272841333746490427929749)
            ·
              refine ⟨5919039437519366738809207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126272841333746490427929749 5919039437519366738809207)
              ·
                refine ⟨8878559156279050108213811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5919039437519366738809207 8878559156279050108213811)
                ·
                  refine ⟨13317838734418575162320717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8878559156279050108213811 13317838734418575162320717)
                  ·
                    refine ⟨4994189525406965685870269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13317838734418575162320717 4994189525406965685870269)
                    ·
                      refine ⟨1872821072027612132201351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4994189525406965685870269 1872821072027612132201351)
                      ·
                        rfl

theorem cell23_3647306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_3647306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647306 prefixEnd_3647306 := by exact prefixLift 3647306
  have htrace : WordTrace (prefixWord ++ tailWord_3647306) baseStart_3647306 baseEnd_3647306 := by
    simpa [prefixWord, tailWord_3647306, baseEnd_3647306] using wordTrace_append hprefix tailTrace_3647306
  have hstable : (prefixWord ++ tailWord_3647306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647306).length < 2 ^ (prefixWord ++ tailWord_3647306).sum := by decide
  have hdescent : baseEnd_3647306 < baseStart_3647306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647324 : List Nat := [2, 2, 4, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_3647324 : Nat := 118140960795 + 3647324 * 2 ^ 59
def prefixEnd_3647324 : Nat := 4983230072969 + 3 ^ 40 * 3647324 * 2
def baseEnd_3647324 : Nat := 1872830314679393061776269

theorem tailTrace_3647324 : CollatzResearch.WordTrace tailWord_3647324 prefixEnd_3647324 1872830314679393061776269 := by
  unfold tailWord_3647324
  simp only [CollatzResearch.WordTrace]
  refine ⟨66514417519187768095822513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88685890025583690794430017 66514417519187768095822513)
  ·
    refine ⟨49885813139390826071866885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66514417519187768095822513 49885813139390826071866885)
    ·
      refine ⟨9353589963635779888475041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49885813139390826071866885 9353589963635779888475041)
      ·
        refine ⟨7015192472726834916356281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9353589963635779888475041 7015192472726834916356281)
        ·
          refine ⟨5261394354545126187267211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7015192472726834916356281 5261394354545126187267211)
          ·
            refine ⟨7892091531817689280900817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5261394354545126187267211 7892091531817689280900817)
            ·
              refine ⟨5919068648863266960675613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7892091531817689280900817 5919068648863266960675613)
              ·
                refine ⟨2219650743323725110253355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5919068648863266960675613 2219650743323725110253355)
                ·
                  refine ⟨3329476114985587665380033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219650743323725110253355 3329476114985587665380033)
                  ·
                    refine ⟨2497107086239190749035025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3329476114985587665380033 2497107086239190749035025)
                    ·
                      refine ⟨1872830314679393061776269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2497107086239190749035025 1872830314679393061776269)
                      ·
                        rfl

theorem cell23_3647324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_3647324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647324 prefixEnd_3647324 := by exact prefixLift 3647324
  have htrace : WordTrace (prefixWord ++ tailWord_3647324) baseStart_3647324 baseEnd_3647324 := by
    simpa [prefixWord, tailWord_3647324, baseEnd_3647324] using wordTrace_append hprefix tailTrace_3647324
  have hstable : (prefixWord ++ tailWord_3647324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647324).length < 2 ^ (prefixWord ++ tailWord_3647324).sum := by decide
  have hdescent : baseEnd_3647324 < baseStart_3647324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647340 : List Nat := [2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 3]
def baseStart_3647340 : Nat := 118140960795 + 3647340 * 2 ^ 59
def prefixEnd_3647340 : Nat := 4983230072969 + 3 ^ 40 * 3647340 * 2
def baseEnd_3647340 : Nat := 1872838530369864999176195

theorem tailTrace_3647340 : CollatzResearch.WordTrace tailWord_3647340 prefixEnd_3647340 1872838530369864999176195 := by
  unfold tailWord_3647340
  simp only [CollatzResearch.WordTrace]
  refine ⟨66514709303158785462113737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88686279070878380616151649 66514709303158785462113737)
  ·
    refine ⟨49886031977369089096585303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66514709303158785462113737 49886031977369089096585303)
    ·
      refine ⟨74829047966053633644877955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49886031977369089096585303 74829047966053633644877955)
      ·
        refine ⟨112243571949080450467316933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74829047966053633644877955 112243571949080450467316933)
        ·
          refine ⟨21045669740452584462621925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112243571949080450467316933 21045669740452584462621925)
          ·
            refine ⟨3946063076334859586741611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21045669740452584462621925 3946063076334859586741611)
            ·
              refine ⟨5919094614502289380112417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3946063076334859586741611 5919094614502289380112417)
              ·
                refine ⟨4439320960876717035084313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5919094614502289380112417 4439320960876717035084313)
                ·
                  refine ⟨3329490720657537776313235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4439320960876717035084313 3329490720657537776313235)
                  ·
                    refine ⟨4994236080986306664469853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3329490720657537776313235 4994236080986306664469853)
                    ·
                      refine ⟨1872838530369864999176195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4994236080986306664469853 1872838530369864999176195)
                      ·
                        rfl

theorem cell23_3647340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 3].length) (baseStart_3647340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647340 prefixEnd_3647340 := by exact prefixLift 3647340
  have htrace : WordTrace (prefixWord ++ tailWord_3647340) baseStart_3647340 baseEnd_3647340 := by
    simpa [prefixWord, tailWord_3647340, baseEnd_3647340] using wordTrace_append hprefix tailTrace_3647340
  have hstable : (prefixWord ++ tailWord_3647340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647340).length < 2 ^ (prefixWord ++ tailWord_3647340).sum := by decide
  have hdescent : baseEnd_3647340 < baseStart_3647340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647363 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 1, 4, 2]
def baseStart_3647363 : Nat := 118140960795 + 3647363 * 2 ^ 59
def prefixEnd_3647363 : Nat := 4983230072969 + 3 ^ 40 * 3647363 * 2
def baseEnd_3647363 : Nat := 1872850340424918409188589

theorem tailTrace_3647363 : CollatzResearch.WordTrace tailWord_3647363 prefixEnd_3647363 1872850340424918409188589 := by
  unfold tailWord_3647363
  simp only [CollatzResearch.WordTrace]
  refine ⟨133030257485234245852314743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88686838323489497234876495 133030257485234245852314743)
  ·
    refine ⟨199545386227851368778472115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133030257485234245852314743 199545386227851368778472115)
    ·
      refine ⟨299318079341777053167708173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199545386227851368778472115 299318079341777053167708173)
      ·
        refine ⟨112244279753166394937890565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299318079341777053167708173 112244279753166394937890565)
        ·
          refine ⟨21045802453718699050854481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112244279753166394937890565 21045802453718699050854481)
          ·
            refine ⟨15784351840289024288140861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21045802453718699050854481 15784351840289024288140861)
            ·
              refine ⟨5919131940108384108052823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15784351840289024288140861 5919131940108384108052823)
              ·
                refine ⟨8878697910162576162079235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5919131940108384108052823 8878697910162576162079235)
                ·
                  refine ⟨13318046865243864243118853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8878697910162576162079235 13318046865243864243118853)
                  ·
                    refine ⟨2497133787233224545584785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13318046865243864243118853 2497133787233224545584785)
                    ·
                      refine ⟨1872850340424918409188589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2497133787233224545584785 1872850340424918409188589)
                      ·
                        rfl

theorem cell23_3647363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 4, 2].length) (baseStart_3647363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647363 prefixEnd_3647363 := by exact prefixLift 3647363
  have htrace : WordTrace (prefixWord ++ tailWord_3647363) baseStart_3647363 baseEnd_3647363 := by
    simpa [prefixWord, tailWord_3647363, baseEnd_3647363] using wordTrace_append hprefix tailTrace_3647363
  have hstable : (prefixWord ++ tailWord_3647363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647363).length < 2 ^ (prefixWord ++ tailWord_3647363).sum := by decide
  have hdescent : baseEnd_3647363 < baseStart_3647363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647369 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 7]
def baseStart_3647369 : Nat := 118140960795 + 3647369 * 2 ^ 59
def prefixEnd_3647369 : Nat := 4983230072969 + 3 ^ 40 * 3647369 * 2
def baseEnd_3647369 : Nat := 208094824589871709523729

theorem tailTrace_3647369 : CollatzResearch.WordTrace tailWord_3647369 prefixEnd_3647369 208094824589871709523729 := by
  unfold tailWord_3647369
  simp only [CollatzResearch.WordTrace]
  refine ⟨133030476323212508877033161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88686984215475005918022107 133030476323212508877033161)
  ·
    refine ⟨99772857242409381657774871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133030476323212508877033161 99772857242409381657774871)
    ·
      refine ⟨149659285863614072486662307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99772857242409381657774871 149659285863614072486662307)
      ·
        refine ⟨224488928795421108729993461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149659285863614072486662307 224488928795421108729993461)
        ·
          refine ⟨21045837074570728943436887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224488928795421108729993461 21045837074570728943436887)
          ·
            refine ⟨31568755611856093415155331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21045837074570728943436887 31568755611856093415155331)
            ·
              refine ⟨47353133417784140122732997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31568755611856093415155331 47353133417784140122732997)
              ·
                refine ⟨8878712515834526273012437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47353133417784140122732997 8878712515834526273012437)
                ·
                  refine ⟨208094824589871709523729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8878712515834526273012437 208094824589871709523729)
                  ·
                    rfl

theorem cell23_3647369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 7].length) (baseStart_3647369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647369 prefixEnd_3647369 := by exact prefixLift 3647369
  have htrace : WordTrace (prefixWord ++ tailWord_3647369) baseStart_3647369 baseEnd_3647369 := by
    simpa [prefixWord, tailWord_3647369, baseEnd_3647369] using wordTrace_append hprefix tailTrace_3647369
  have hstable : (prefixWord ++ tailWord_3647369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647369).length < 2 ^ (prefixWord ++ tailWord_3647369).sum := by decide
  have hdescent : baseEnd_3647369 < baseStart_3647369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647380 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_3647380 : Nat := 118140960795 + 3647380 * 2 ^ 59
def prefixEnd_3647380 : Nat := 4983230072969 + 3 ^ 40 * 3647380 * 2
def baseEnd_3647380 : Nat := 1872859069596044842676011

theorem tailTrace_3647380 : CollatzResearch.WordTrace tailWord_3647380 prefixEnd_3647380 1872859069596044842676011 := by
  unfold tailWord_3647380
  simp only [CollatzResearch.WordTrace]
  refine ⟨66515438763086328877841797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88687251684115105170455729 66515438763086328877841797)
  ·
    refine ⟨12471644768078686664595337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66515438763086328877841797 12471644768078686664595337)
    ·
      refine ⟨9353733576059014998446503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12471644768078686664595337 9353733576059014998446503)
      ·
        refine ⟨14030600364088522497669755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9353733576059014998446503 14030600364088522497669755)
        ·
          refine ⟨21045900546132783746504633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14030600364088522497669755 21045900546132783746504633)
          ·
            refine ⟨15784425409599587809878475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21045900546132783746504633 15784425409599587809878475)
            ·
              refine ⟨23676638114399381714817713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15784425409599587809878475 23676638114399381714817713)
              ·
                refine ⟨17757478585799536286113285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23676638114399381714817713 17757478585799536286113285)
                ·
                  refine ⟨3329527234837413053646241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17757478585799536286113285 3329527234837413053646241)
                  ·
                    refine ⟨2497145426128059790234681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3329527234837413053646241 2497145426128059790234681)
                    ·
                      refine ⟨1872859069596044842676011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2497145426128059790234681 1872859069596044842676011)
                      ·
                        rfl

theorem cell23_3647380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_3647380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647380 prefixEnd_3647380 := by exact prefixLift 3647380
  have htrace : WordTrace (prefixWord ++ tailWord_3647380) baseStart_3647380 baseEnd_3647380 := by
    simpa [prefixWord, tailWord_3647380, baseEnd_3647380] using wordTrace_append hprefix tailTrace_3647380
  have hstable : (prefixWord ++ tailWord_3647380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647380).length < 2 ^ (prefixWord ++ tailWord_3647380).sum := by decide
  have hdescent : baseEnd_3647380 < baseStart_3647380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647470 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_3647470 : Nat := 118140960795 + 3647470 * 2 ^ 59
def prefixEnd_3647470 : Nat := 4983230072969 + 3 ^ 40 * 3647470 * 2
def baseEnd_3647470 : Nat := 1872905282854949490550597

theorem tailTrace_3647470 : CollatzResearch.WordTrace tailWord_3647470 prefixEnd_3647470 1872905282854949490550597 := by
  unfold tailWord_3647470
  simp only [CollatzResearch.WordTrace]
  refine ⟨16629270011980825390807483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88689440063897735417639909 16629270011980825390807483)
  ·
    refine ⟨24943905017971238086211225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16629270011980825390807483 24943905017971238086211225)
    ·
      refine ⟨18707928763478428564658419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24943905017971238086211225 18707928763478428564658419)
      ·
        refine ⟨28061893145217642846987629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18707928763478428564658419 28061893145217642846987629)
        ·
          refine ⟨10523209929456616067620361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28061893145217642846987629 10523209929456616067620361)
          ·
            refine ⟨7892407447092462050715271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10523209929456616067620361 7892407447092462050715271)
            ·
              refine ⟨11838611170638693076072907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7892407447092462050715271 11838611170638693076072907)
              ·
                refine ⟨17757916755958039614109361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11838611170638693076072907 17757916755958039614109361)
                ·
                  refine ⟨13318437566968529710582021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17757916755958039614109361 13318437566968529710582021)
                  ·
                    refine ⟨2497207043806599320734129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13318437566968529710582021 2497207043806599320734129)
                    ·
                      refine ⟨1872905282854949490550597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2497207043806599320734129 1872905282854949490550597)
                      ·
                        rfl

theorem cell23_3647470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_3647470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647470 prefixEnd_3647470 := by exact prefixLift 3647470
  have htrace : WordTrace (prefixWord ++ tailWord_3647470) baseStart_3647470 baseEnd_3647470 := by
    simpa [prefixWord, tailWord_3647470, baseEnd_3647470] using wordTrace_append hprefix tailTrace_3647470
  have hstable : (prefixWord ++ tailWord_3647470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647470).length < 2 ^ (prefixWord ++ tailWord_3647470).sum := by decide
  have hdescent : baseEnd_3647470 < baseStart_3647470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647513 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 4, 3, 2]
def baseStart_3647513 : Nat := 118140960795 + 3647513 * 2 ^ 59
def prefixEnd_3647513 : Nat := 4983230072969 + 3 ^ 40 * 3647513 * 2
def baseEnd_3647513 : Nat := 1872927362523092822312899

theorem tailTrace_3647513 : CollatzResearch.WordTrace tailWord_3647513 prefixEnd_3647513 1872927362523092822312899 := by
  unfold tailWord_3647513
  simp only [CollatzResearch.WordTrace]
  refine ⟨133035728434690821470275193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88690485623127214313516795 133035728434690821470275193)
  ·
    refine ⟨99776796326018116102706395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133035728434690821470275193 99776796326018116102706395)
    ·
      refine ⟨149665194489027174154059593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99776796326018116102706395 149665194489027174154059593)
      ·
        refine ⟨112248895866770380615544695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149665194489027174154059593 112248895866770380615544695)
        ·
          refine ⟨168373343800155570923317043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112248895866770380615544695 168373343800155570923317043)
          ·
            refine ⟨252560015700233356384975565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168373343800155570923317043 252560015700233356384975565)
            ·
              refine ⟨94710005887587508644365837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252560015700233356384975565 94710005887587508644365837)
              ·
                refine ⟨35516252207845315741637189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94710005887587508644365837 35516252207845315741637189)
                ·
                  refine ⟨6659297288970996701556973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35516252207845315741637189 6659297288970996701556973)
                  ·
                    refine ⟨2497236483364123763083865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6659297288970996701556973 2497236483364123763083865)
                    ·
                      refine ⟨1872927362523092822312899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2497236483364123763083865 1872927362523092822312899)
                      ·
                        rfl

theorem cell23_3647513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 3, 2].length) (baseStart_3647513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647513 prefixEnd_3647513 := by exact prefixLift 3647513
  have htrace : WordTrace (prefixWord ++ tailWord_3647513) baseStart_3647513 baseEnd_3647513 := by
    simpa [prefixWord, tailWord_3647513, baseEnd_3647513] using wordTrace_append hprefix tailTrace_3647513
  have hstable : (prefixWord ++ tailWord_3647513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647513).length < 2 ^ (prefixWord ++ tailWord_3647513).sum := by decide
  have hdescent : baseEnd_3647513 < baseStart_3647513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647527 : List Nat := [1, 1, 7, 1, 2, 1, 3, 1, 6]
def baseStart_3647527 : Nat := 118140960795 + 3647527 * 2 ^ 59
def prefixEnd_3647527 : Nat := 4983230072969 + 3 ^ 40 * 3647527 * 2
def baseEnd_3647527 : Nat := 208103839028028418615315

theorem tailTrace_3647527 : CollatzResearch.WordTrace tailWord_3647527 prefixEnd_3647527 208103839028028418615315 := by
  unfold tailWord_3647527
  simp only [CollatzResearch.WordTrace]
  refine ⟨133036239056640101861284835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88690826037760067907523223 133036239056640101861284835)
  ·
    refine ⟨199554358584960152791927253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133036239056640101861284835 199554358584960152791927253)
    ·
      refine ⟨4677055279335003581060795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 199554358584960152791927253 4677055279335003581060795)
      ·
        refine ⟨7015582919002505371591193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4677055279335003581060795 7015582919002505371591193)
        ·
          refine ⟨5261687189251879028693395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7015582919002505371591193 5261687189251879028693395)
          ·
            refine ⟨7892530783877818543040093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5261687189251879028693395 7892530783877818543040093)
            ·
              refine ⟨2959699043954181953640035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7892530783877818543040093 2959699043954181953640035)
              ·
                refine ⟨4439548565931272930460053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2959699043954181953640035 4439548565931272930460053)
                ·
                  refine ⟨208103839028028418615315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4439548565931272930460053 208103839028028418615315)
                  ·
                    rfl

theorem cell23_3647527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 6].length) (baseStart_3647527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647527 prefixEnd_3647527 := by exact prefixLift 3647527
  have htrace : WordTrace (prefixWord ++ tailWord_3647527) baseStart_3647527 baseEnd_3647527 := by
    simpa [prefixWord, tailWord_3647527, baseEnd_3647527] using wordTrace_append hprefix tailTrace_3647527
  have hstable : (prefixWord ++ tailWord_3647527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647527).length < 2 ^ (prefixWord ++ tailWord_3647527).sum := by decide
  have hdescent : baseEnd_3647527 < baseStart_3647527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647530 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_3647530 : Nat := 118140960795 + 3647530 * 2 ^ 59
def prefixEnd_3647530 : Nat := 4983230072969 + 3 ^ 40 * 3647530 * 2
def baseEnd_3647530 : Nat := 1872936091694219255800321

theorem tailTrace_3647530 : CollatzResearch.WordTrace tailWord_3647530 prefixEnd_3647530 1872936091694219255800321 := by
  unfold tailWord_3647530
  simp only [CollatzResearch.WordTrace]
  refine ⟨33259087118907308343411011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88690898983752822249096029 33259087118907308343411011)
  ·
    refine ⟨49888630678360962515116517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33259087118907308343411011 49888630678360962515116517)
    ·
      refine ⟨9354118252192680471584347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49888630678360962515116517 9354118252192680471584347)
      ·
        refine ⟨14031177378289020707376521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9354118252192680471584347 14031177378289020707376521)
        ·
          refine ⟨10523383033716765530532391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14031177378289020707376521 10523383033716765530532391)
          ·
            refine ⟨15785074550575148295798587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10523383033716765530532391 15785074550575148295798587)
            ·
              refine ⟨23677611825862722443697881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15785074550575148295798587 23677611825862722443697881)
              ·
                refine ⟨17758208869397041832773411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23677611825862722443697881 17758208869397041832773411)
                ·
                  refine ⟨26637313304095562749160117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17758208869397041832773411 26637313304095562749160117)
                  ·
                    refine ⟨2497248122258959007733761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26637313304095562749160117 2497248122258959007733761)
                    ·
                      refine ⟨1872936091694219255800321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2497248122258959007733761 1872936091694219255800321)
                      ·
                        rfl

theorem cell23_3647530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_3647530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647530 prefixEnd_3647530 := by exact prefixLift 3647530
  have htrace : WordTrace (prefixWord ++ tailWord_3647530) baseStart_3647530 baseEnd_3647530 := by
    simpa [prefixWord, tailWord_3647530, baseEnd_3647530] using wordTrace_append hprefix tailTrace_3647530
  have hstable : (prefixWord ++ tailWord_3647530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647530).length < 2 ^ (prefixWord ++ tailWord_3647530).sum := by decide
  have hdescent : baseEnd_3647530 < baseStart_3647530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647543 : List Nat := [1, 1, 3, 1, 2, 2, 3, 4, 1, 1, 4]
def baseStart_3647543 : Nat := 118140960795 + 3647543 * 2 ^ 59
def prefixEnd_3647543 : Nat := 4983230072969 + 3 ^ 40 * 3647543 * 2
def baseEnd_3647543 : Nat := 1872942766942727704937761

theorem tailTrace_3647543 : CollatzResearch.WordTrace tailWord_3647543 prefixEnd_3647543 1872942766942727704937761 := by
  unfold tailWord_3647543
  simp only [CollatzResearch.WordTrace]
  refine ⟨133036822624582136593867283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88691215083054757729244855 133036822624582136593867283)
  ·
    refine ⟨199555233936873204890800925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133036822624582136593867283 199555233936873204890800925)
    ·
      refine ⟨74833212726327451834050347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199555233936873204890800925 74833212726327451834050347)
      ·
        refine ⟨112249819089491177751075521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74833212726327451834050347 112249819089491177751075521)
        ·
          refine ⟨84187364317118383313306641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112249819089491177751075521 84187364317118383313306641)
          ·
            refine ⟨63140523237838787484979981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84187364317118383313306641 63140523237838787484979981)
            ·
              refine ⟨23677696214189545306867493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63140523237838787484979981 23677696214189545306867493)
              ·
                refine ⟨4439568040160539745037655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23677696214189545306867493 4439568040160539745037655)
                ·
                  refine ⟨6659352060240809617556483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4439568040160539745037655 6659352060240809617556483)
                  ·
                    refine ⟨9989028090361214426334725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6659352060240809617556483 9989028090361214426334725)
                    ·
                      refine ⟨1872942766942727704937761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9989028090361214426334725 1872942766942727704937761)
                      ·
                        rfl

theorem cell23_3647543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_3647543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647543 prefixEnd_3647543 := by exact prefixLift 3647543
  have htrace : WordTrace (prefixWord ++ tailWord_3647543) baseStart_3647543 baseEnd_3647543 := by
    simpa [prefixWord, tailWord_3647543, baseEnd_3647543] using wordTrace_append hprefix tailTrace_3647543
  have hstable : (prefixWord ++ tailWord_3647543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647543).length < 2 ^ (prefixWord ++ tailWord_3647543).sum := by decide
  have hdescent : baseEnd_3647543 < baseStart_3647543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647546 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_3647546 : Nat := 118140960795 + 3647546 * 2 ^ 59
def prefixEnd_3647546 : Nat := 4983230072969 + 3 ^ 40 * 3647546 * 2
def baseEnd_3647546 : Nat := 1872944307384691193200247

theorem tailTrace_3647546 : CollatzResearch.WordTrace tailWord_3647546 prefixEnd_3647546 1872944307384691193200247 := by
  unfold tailWord_3647546
  simp only [CollatzResearch.WordTrace]
  refine ⟨33259233010892817026556623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88691288029047512070817661 33259233010892817026556623)
  ·
    refine ⟨49888849516339225539834935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33259233010892817026556623 49888849516339225539834935)
    ·
      refine ⟨74833274274508838309752403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49888849516339225539834935 74833274274508838309752403)
      ·
        refine ⟨112249911411763257464628605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74833274274508838309752403 112249911411763257464628605)
        ·
          refine ⟨42093716779411221549235727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112249911411763257464628605 42093716779411221549235727)
          ·
            refine ⟨63140575169116832323853591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42093716779411221549235727 63140575169116832323853591)
            ·
              refine ⟨94710862753675248485780387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63140575169116832323853591 94710862753675248485780387)
              ·
                refine ⟨142066294130512872728670581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94710862753675248485780387 142066294130512872728670581)
                ·
                  refine ⟨13318715074735581818312867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142066294130512872728670581 13318715074735581818312867)
                  ·
                    refine ⟨19978072612103372727469301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13318715074735581818312867 19978072612103372727469301)
                    ·
                      refine ⟨1872944307384691193200247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19978072612103372727469301 1872944307384691193200247)
                      ·
                        rfl

theorem cell23_3647546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_3647546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647546 prefixEnd_3647546 := by exact prefixLift 3647546
  have htrace : WordTrace (prefixWord ++ tailWord_3647546) baseStart_3647546 baseEnd_3647546 := by
    simpa [prefixWord, tailWord_3647546, baseEnd_3647546] using wordTrace_append hprefix tailTrace_3647546
  have hstable : (prefixWord ++ tailWord_3647546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647546).length < 2 ^ (prefixWord ++ tailWord_3647546).sum := by decide
  have hdescent : baseEnd_3647546 < baseStart_3647546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647566 : List Nat := [4, 1, 1, 1, 1, 4, 11]
def baseStart_3647566 : Nat := 118140960795 + 3647566 * 2 ^ 59
def prefixEnd_3647566 : Nat := 4983230072969 + 3 ^ 40 * 3647566 * 2
def baseEnd_3647566 : Nat := 23122896012318285369755

theorem tailTrace_3647566 : CollatzResearch.WordTrace tailWord_3647566 prefixEnd_3647566 23122896012318285369755 := by
  unfold tailWord_3647566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16629707687937351440244319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88691774335665874347969701 16629707687937351440244319)
  ·
    refine ⟨24944561531906027160366479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16629707687937351440244319 24944561531906027160366479)
    ·
      refine ⟨37416842297859040740549719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24944561531906027160366479 37416842297859040740549719)
      ·
        refine ⟨56125263446788561110824579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37416842297859040740549719 56125263446788561110824579)
        ·
          refine ⟨84187895170182841666236869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56125263446788561110824579 84187895170182841666236869)
          ·
            refine ⟨15785230344409282812419413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84187895170182841666236869 15785230344409282812419413)
            ·
              refine ⟨23122896012318285369755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15785230344409282812419413 23122896012318285369755)
              ·
                rfl

theorem cell23_3647566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 11].length) (baseStart_3647566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647566 prefixEnd_3647566 := by exact prefixLift 3647566
  have htrace : WordTrace (prefixWord ++ tailWord_3647566) baseStart_3647566 baseEnd_3647566 := by
    simpa [prefixWord, tailWord_3647566, baseEnd_3647566] using wordTrace_append hprefix tailTrace_3647566
  have hstable : (prefixWord ++ tailWord_3647566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647566).length < 2 ^ (prefixWord ++ tailWord_3647566).sum := by decide
  have hdescent : baseEnd_3647566 < baseStart_3647566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647593 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 1, 3, 3]
def baseStart_3647593 : Nat := 118140960795 + 3647593 * 2 ^ 59
def prefixEnd_3647593 : Nat := 4983230072969 + 3 ^ 40 * 3647593 * 2
def baseEnd_3647593 : Nat := 1872968440975452509312531

theorem tailTrace_3647593 : CollatzResearch.WordTrace tailWord_3647593 prefixEnd_3647593 1872968440975452509312531 := by
  unfold tailWord_3647593
  simp only [CollatzResearch.WordTrace]
  refine ⟨133038646274400995133187433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88692430849600663422124955 133038646274400995133187433)
  ·
    refine ⟨99778984705800746349890575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133038646274400995133187433 99778984705800746349890575)
    ·
      refine ⟨149668477058701119524835863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99778984705800746349890575 149668477058701119524835863)
      ·
        refine ⟨224502715588051679287253795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149668477058701119524835863 224502715588051679287253795)
        ·
          refine ⟨336754073382077518930880693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224502715588051679287253795 336754073382077518930880693)
          ·
            refine ⟨31570694379569767399770065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 336754073382077518930880693 31570694379569767399770065)
            ·
              refine ⟨23678020784677325549827549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31570694379569767399770065 23678020784677325549827549)
              ·
                refine ⟨8879257794253997081185331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23678020784677325549827549 8879257794253997081185331)
                ·
                  refine ⟨13318886691380995621777997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8879257794253997081185331 13318886691380995621777997)
                  ·
                    refine ⟨4994582509267873358166749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13318886691380995621777997 4994582509267873358166749)
                    ·
                      refine ⟨1872968440975452509312531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4994582509267873358166749 1872968440975452509312531)
                      ·
                        rfl

theorem cell23_3647593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 3, 3].length) (baseStart_3647593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647593 prefixEnd_3647593 := by exact prefixLift 3647593
  have htrace : WordTrace (prefixWord ++ tailWord_3647593) baseStart_3647593 baseEnd_3647593 := by
    simpa [prefixWord, tailWord_3647593, baseEnd_3647593] using wordTrace_append hprefix tailTrace_3647593
  have hstable : (prefixWord ++ tailWord_3647593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647593).length < 2 ^ (prefixWord ++ tailWord_3647593).sum := by decide
  have hdescent : baseEnd_3647593 < baseStart_3647593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647594 : List Nat := [3, 1, 3, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_3647594 : Nat := 118140960795 + 3647594 * 2 ^ 59
def prefixEnd_3647594 : Nat := 4983230072969 + 3 ^ 40 * 3647594 * 2
def baseEnd_3647594 : Nat := 1872968954456107005400027

theorem tailTrace_3647594 : CollatzResearch.WordTrace tailWord_3647594 prefixEnd_3647594 1872968954456107005400027 := by
  unfold tailWord_3647594
  simp only [CollatzResearch.WordTrace]
  refine ⟨33259670686849343075993459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88692455164931581535982557 33259670686849343075993459)
  ·
    refine ⟨49889506030274014613990189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33259670686849343075993459 49889506030274014613990189)
    ·
      refine ⟨18708564761352755480246321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49889506030274014613990189 18708564761352755480246321)
      ·
        refine ⟨14031423571014566610184741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18708564761352755480246321 14031423571014566610184741)
        ·
          refine ⟨2630891919565231239409639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14031423571014566610184741 2630891919565231239409639)
          ·
            refine ⟨3946337879347846859114459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630891919565231239409639 3946337879347846859114459)
            ·
              refine ⟨5919506819021770288671689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3946337879347846859114459 5919506819021770288671689)
              ·
                refine ⟨4439630114266327716503767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5919506819021770288671689 4439630114266327716503767)
                ·
                  refine ⟨6659445171399491574755651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4439630114266327716503767 6659445171399491574755651)
                  ·
                    refine ⟨9989167757099237362133477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6659445171399491574755651 9989167757099237362133477)
                    ·
                      refine ⟨1872968954456107005400027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9989167757099237362133477 1872968954456107005400027)
                      ·
                        rfl

theorem cell23_3647594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_3647594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647594 prefixEnd_3647594 := by exact prefixLift 3647594
  have htrace : WordTrace (prefixWord ++ tailWord_3647594) baseStart_3647594 baseEnd_3647594 := by
    simpa [prefixWord, tailWord_3647594, baseEnd_3647594] using wordTrace_append hprefix tailTrace_3647594
  have hstable : (prefixWord ++ tailWord_3647594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647594).length < 2 ^ (prefixWord ++ tailWord_3647594).sum := by decide
  have hdescent : baseEnd_3647594 < baseStart_3647594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647653 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 2, 4, 3]
def baseStart_3647653 : Nat := 118140960795 + 3647653 * 2 ^ 59
def prefixEnd_3647653 : Nat := 4983230072969 + 3 ^ 40 * 3647653 * 2
def baseEnd_3647653 : Nat := 1872999249814722274562255

theorem tailTrace_3647653 : CollatzResearch.WordTrace tailWord_3647653 prefixEnd_3647653 1872999249814722274562255 := by
  unfold tailWord_3647653
  simp only [CollatzResearch.WordTrace]
  refine ⟨133040834654183625380371613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88693889769455750253581075 133040834654183625380371613)
  ·
    refine ⟨49890312995318859517639355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133040834654183625380371613 49890312995318859517639355)
    ·
      refine ⟨74835469492978289276459033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49890312995318859517639355 74835469492978289276459033)
      ·
        refine ⟨56126602119733716957344275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74835469492978289276459033 56126602119733716957344275)
        ·
          refine ⟨84189903179600575436016413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56126602119733716957344275 84189903179600575436016413)
          ·
            refine ⟨31571213692350215788506155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84189903179600575436016413 31571213692350215788506155)
            ·
              refine ⟨47356820538525323682759233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31571213692350215788506155 47356820538525323682759233)
              ·
                refine ⟨35517615403893992762069425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47356820538525323682759233 35517615403893992762069425)
                ·
                  refine ⟨26638211552920494571552069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35517615403893992762069425 26638211552920494571552069)
                  ·
                    refine ⟨4994664666172592732166013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26638211552920494571552069 4994664666172592732166013)
                    ·
                      refine ⟨1872999249814722274562255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4994664666172592732166013 1872999249814722274562255)
                      ·
                        rfl

theorem cell23_3647653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_3647653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647653 prefixEnd_3647653 := by exact prefixLift 3647653
  have htrace : WordTrace (prefixWord ++ tailWord_3647653) baseStart_3647653 baseEnd_3647653 := by
    simpa [prefixWord, tailWord_3647653, baseEnd_3647653] using wordTrace_append hprefix tailTrace_3647653
  have hstable : (prefixWord ++ tailWord_3647653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647653).length < 2 ^ (prefixWord ++ tailWord_3647653).sum := by decide
  have hdescent : baseEnd_3647653 < baseStart_3647653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647684 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 4, 2, 2]
def baseStart_3647684 : Nat := 118140960795 + 3647684 * 2 ^ 59
def prefixEnd_3647684 : Nat := 4983230072969 + 3 ^ 40 * 3647684 * 2
def baseEnd_3647684 : Nat := 1873015167715011653274613

theorem tailTrace_3647684 : CollatzResearch.WordTrace tailWord_3647684 prefixEnd_3647684 1873015167715011653274613 := by
  unfold tailWord_3647684
  simp only [CollatzResearch.WordTrace]
  refine ⟨66520982658535658837375053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88694643544714211783166737 66520982658535658837375053)
  ·
    refine ⟨24945368496950872064015645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66520982658535658837375053 24945368496950872064015645)
    ·
      refine ⟨9354513186356577024005867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24945368496950872064015645 9354513186356577024005867)
      ·
        refine ⟨14031769779534865536008801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9354513186356577024005867 14031769779534865536008801)
        ·
          refine ⟨10523827334651149152006601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14031769779534865536008801 10523827334651149152006601)
          ·
            refine ⟨7892870500988361864004951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10523827334651149152006601 7892870500988361864004951)
            ·
              refine ⟨11839305751482542796007427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7892870500988361864004951 11839305751482542796007427)
              ·
                refine ⟨17758958627223814194011141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11839305751482542796007427 17758958627223814194011141)
                ·
                  refine ⟨3329804742604465161377089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17758958627223814194011141 3329804742604465161377089)
                  ·
                    refine ⟨2497353556953348871032817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3329804742604465161377089 2497353556953348871032817)
                    ·
                      refine ⟨1873015167715011653274613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2497353556953348871032817 1873015167715011653274613)
                      ·
                        rfl

theorem cell23_3647684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_3647684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647684 prefixEnd_3647684 := by exact prefixLift 3647684
  have htrace : WordTrace (prefixWord ++ tailWord_3647684) baseStart_3647684 baseEnd_3647684 := by
    simpa [prefixWord, tailWord_3647684, baseEnd_3647684] using wordTrace_append hprefix tailTrace_3647684
  have hstable : (prefixWord ++ tailWord_3647684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647684).length < 2 ^ (prefixWord ++ tailWord_3647684).sum := by decide
  have hdescent : baseEnd_3647684 < baseStart_3647684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647690 : List Nat := [3, 1, 2, 1, 3, 1, 1, 6, 5]
def baseStart_3647690 : Nat := 118140960795 + 3647690 * 2 ^ 59
def prefixEnd_3647690 : Nat := 4983230072969 + 3 ^ 40 * 3647690 * 2
def baseEnd_3647690 : Nat := 208113138733215403311065

theorem tailTrace_3647690 : CollatzResearch.WordTrace tailWord_3647690 prefixEnd_3647690 208113138733215403311065 := by
  unfold tailWord_3647690
  simp only [CollatzResearch.WordTrace]
  refine ⟨33260546038762395174867131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88694789436699720466312349 33260546038762395174867131)
  ·
    refine ⟨49890819058143592762300697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33260546038762395174867131 49890819058143592762300697)
    ·
      refine ⟨37418114293607694571725523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49890819058143592762300697 37418114293607694571725523)
      ·
        refine ⟨56127171440411541857588285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37418114293607694571725523 56127171440411541857588285)
        ·
          refine ⟨21047689290154328196595607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56127171440411541857588285 21047689290154328196595607)
          ·
            refine ⟨31571533935231492294893411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21047689290154328196595607 31571533935231492294893411)
            ·
              refine ⟨47357300902847238442340117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31571533935231492294893411 47357300902847238442340117)
              ·
                refine ⟨2219873479820964301984693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47357300902847238442340117 2219873479820964301984693)
                ·
                  refine ⟨208113138733215403311065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2219873479820964301984693 208113138733215403311065)
                  ·
                    rfl

theorem cell23_3647690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 5].length) (baseStart_3647690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647690 prefixEnd_3647690 := by exact prefixLift 3647690
  have htrace : WordTrace (prefixWord ++ tailWord_3647690) baseStart_3647690 baseEnd_3647690 := by
    simpa [prefixWord, tailWord_3647690, baseEnd_3647690] using wordTrace_append hprefix tailTrace_3647690
  have hstable : (prefixWord ++ tailWord_3647690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647690).length < 2 ^ (prefixWord ++ tailWord_3647690).sum := by decide
  have hdescent : baseEnd_3647690 < baseStart_3647690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647701 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 1, 4, 2]
def baseStart_3647701 : Nat := 118140960795 + 3647701 * 2 ^ 59
def prefixEnd_3647701 : Nat := 4983230072969 + 3 ^ 40 * 3647701 * 2
def baseEnd_3647701 : Nat := 1873023896886138086762035

theorem tailTrace_3647701 : CollatzResearch.WordTrace tailWord_3647701 prefixEnd_3647701 1873023896886138086762035 := by
  unfold tailWord_3647701
  simp only [CollatzResearch.WordTrace]
  refine ⟨133042585358009729578118957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88695056905339819718745971 133042585358009729578118957)
  ·
    refine ⟨49890969509253648591794609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133042585358009729578118957 49890969509253648591794609)
    ·
      refine ⟨37418227131940236443845957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49890969509253648591794609 37418227131940236443845957)
      ·
        refine ⟨7015917587238794333221117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37418227131940236443845957 7015917587238794333221117)
        ·
          refine ⟨2630969095214547874957919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7015917587238794333221117 2630969095214547874957919)
          ·
            refine ⟨3946453642821821812436879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630969095214547874957919 3946453642821821812436879)
            ·
              refine ⟨5919680464232732718655319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3946453642821821812436879 5919680464232732718655319)
              ·
                refine ⟨8879520696349099077982979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5919680464232732718655319 8879520696349099077982979)
                ·
                  refine ⟨13319281044523648616974469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8879520696349099077982979 13319281044523648616974469)
                  ·
                    refine ⟨2497365195848184115682713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13319281044523648616974469 2497365195848184115682713)
                    ·
                      refine ⟨1873023896886138086762035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2497365195848184115682713 1873023896886138086762035)
                      ·
                        rfl

theorem cell23_3647701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_3647701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647701 prefixEnd_3647701 := by exact prefixLift 3647701
  have htrace : WordTrace (prefixWord ++ tailWord_3647701) baseStart_3647701 baseEnd_3647701 := by
    simpa [prefixWord, tailWord_3647701, baseEnd_3647701] using wordTrace_append hprefix tailTrace_3647701
  have hstable : (prefixWord ++ tailWord_3647701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647701).length < 2 ^ (prefixWord ++ tailWord_3647701).sum := by decide
  have hdescent : baseEnd_3647701 < baseStart_3647701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647723 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 4]
def baseStart_3647723 : Nat := 118140960795 + 3647723 * 2 ^ 59
def prefixEnd_3647723 : Nat := 4983230072969 + 3 ^ 40 * 3647723 * 2
def baseEnd_3647723 : Nat := 1873035193460537000686933

theorem tailTrace_3647723 : CollatzResearch.WordTrace tailWord_3647723 prefixEnd_3647723 1873035193460537000686933 := by
  unfold tailWord_3647723
  simp only [CollatzResearch.WordTrace]
  refine ⟨133043387763930027335419823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88695591842620018223613215 133043387763930027335419823)
  ·
    refine ⟨199565081645895041003129735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133043387763930027335419823 199565081645895041003129735)
    ·
      refine ⟨299347622468842561504694603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199565081645895041003129735 299347622468842561504694603)
      ·
        refine ⟨449021433703263842257041905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299347622468842561504694603 449021433703263842257041905)
        ·
          refine ⟨336766075277447881692781429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449021433703263842257041905 336766075277447881692781429)
          ·
            refine ⟨31571819557260738908698259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 336766075277447881692781429 31571819557260738908698259)
            ·
              refine ⟨47357729335891108363047389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31571819557260738908698259 47357729335891108363047389)
              ·
                refine ⟨17759148500959165636142771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47357729335891108363047389 17759148500959165636142771)
                ·
                  refine ⟨26638722751438748454214157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17759148500959165636142771 26638722751438748454214157)
                  ·
                    refine ⟨9989521031789530670330309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26638722751438748454214157 9989521031789530670330309)
                    ·
                      refine ⟨1873035193460537000686933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9989521031789530670330309 1873035193460537000686933)
                      ·
                        rfl

theorem cell23_3647723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 4].length) (baseStart_3647723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647723 prefixEnd_3647723 := by exact prefixLift 3647723
  have htrace : WordTrace (prefixWord ++ tailWord_3647723) baseStart_3647723 baseEnd_3647723 := by
    simpa [prefixWord, tailWord_3647723, baseEnd_3647723] using wordTrace_append hprefix tailTrace_3647723
  have hstable : (prefixWord ++ tailWord_3647723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647723).length < 2 ^ (prefixWord ++ tailWord_3647723).sum := by decide
  have hdescent : baseEnd_3647723 < baseStart_3647723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647740 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_3647740 : Nat := 118140960795 + 3647740 * 2 ^ 59
def prefixEnd_3647740 : Nat := 4983230072969 + 3 ^ 40 * 3647740 * 2
def baseEnd_3647740 : Nat := 1873043922631663434174355

theorem tailTrace_3647740 : CollatzResearch.WordTrace tailWord_3647740 prefixEnd_3647740 1873043922631663434174355 := by
  unfold tailWord_3647740
  simp only [CollatzResearch.WordTrace]
  refine ⟨66522003902434219619394337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88696005203245626159192449 66522003902434219619394337)
  ·
    refine ⟨49891502926825664714545753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66522003902434219619394337 49891502926825664714545753)
    ·
      refine ⟨37418627195119248535909315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49891502926825664714545753 37418627195119248535909315)
      ·
        refine ⟨56127940792678872803863973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37418627195119248535909315 56127940792678872803863973)
        ·
          refine ⟨10523988898627288650724495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56127940792678872803863973 10523988898627288650724495)
          ·
            refine ⟨15785983347940932976086743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10523988898627288650724495 15785983347940932976086743)
            ·
              refine ⟨23678975021911399464130115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15785983347940932976086743 23678975021911399464130115)
              ·
                refine ⟨35518462532867099196195173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23678975021911399464130115 35518462532867099196195173)
                ·
                  refine ⟨6659711724912581099286595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35518462532867099196195173 6659711724912581099286595)
                  ·
                    refine ⟨9989567587368871648929893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6659711724912581099286595 9989567587368871648929893)
                    ·
                      refine ⟨1873043922631663434174355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9989567587368871648929893 1873043922631663434174355)
                      ·
                        rfl

theorem cell23_3647740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_3647740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647740 prefixEnd_3647740 := by exact prefixLift 3647740
  have htrace : WordTrace (prefixWord ++ tailWord_3647740) baseStart_3647740 baseEnd_3647740 := by
    simpa [prefixWord, tailWord_3647740, baseEnd_3647740] using wordTrace_append hprefix tailTrace_3647740
  have hstable : (prefixWord ++ tailWord_3647740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647740).length < 2 ^ (prefixWord ++ tailWord_3647740).sum := by decide
  have hdescent : baseEnd_3647740 < baseStart_3647740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647774 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3647774 : Nat := 118140960795 + 3647774 * 2 ^ 59
def prefixEnd_3647774 : Nat := 4983230072969 + 3 ^ 40 * 3647774 * 2
def baseEnd_3647774 : Nat := 1873061380973916301149199

theorem tailTrace_3647774 : CollatzResearch.WordTrace tailWord_3647774 prefixEnd_3647774 1873061380973916301149199 := by
  unfold tailWord_3647774
  simp only [CollatzResearch.WordTrace]
  refine ⟨16630655985843157880690797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88696831924496842030350917 16630655985843157880690797)
  ·
    refine ⟨6236495994691184205259049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16630655985843157880690797 6236495994691184205259049)
    ·
      refine ⟨4677371996018388153944287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6236495994691184205259049 4677371996018388153944287)
      ·
        refine ⟨7016057994027582230916431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4677371996018388153944287 7016057994027582230916431)
        ·
          refine ⟨10524086991041373346374647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7016057994027582230916431 10524086991041373346374647)
          ·
            refine ⟨15786130486562060019561971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10524086991041373346374647 15786130486562060019561971)
            ·
              refine ⟨23679195729843090029342957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15786130486562060019561971 23679195729843090029342957)
              ·
                refine ⟨8879698398691158761003609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23679195729843090029342957 8879698398691158761003609)
                ·
                  refine ⟨6659773799018369070752707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8879698398691158761003609 6659773799018369070752707)
                  ·
                    refine ⟨9989660698527553606129061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6659773799018369070752707 9989660698527553606129061)
                    ·
                      refine ⟨1873061380973916301149199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9989660698527553606129061 1873061380973916301149199)
                      ·
                        rfl

theorem cell23_3647774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3647774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647774 prefixEnd_3647774 := by exact prefixLift 3647774
  have htrace : WordTrace (prefixWord ++ tailWord_3647774) baseStart_3647774 baseEnd_3647774 := by
    simpa [prefixWord, tailWord_3647774, baseEnd_3647774] using wordTrace_append hprefix tailTrace_3647774
  have hstable : (prefixWord ++ tailWord_3647774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647774).length < 2 ^ (prefixWord ++ tailWord_3647774).sum := by decide
  have hdescent : baseEnd_3647774 < baseStart_3647774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647801 : List Nat := [1, 2, 1, 6, 1, 1, 4, 2, 1, 4]
def baseStart_3647801 : Nat := 118140960795 + 3647801 * 2 ^ 59
def prefixEnd_3647801 : Nat := 4983230072969 + 3 ^ 40 * 3647801 * 2
def baseEnd_3647801 : Nat := 624358414983862565170525

theorem tailTrace_3647801 : CollatzResearch.WordTrace tailWord_3647801 prefixEnd_3647801 624358414983862565170525 := by
  unfold tailWord_3647801
  simp only [CollatzResearch.WordTrace]
  refine ⟨133046232657647446656759257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88697488438431631104506171 133046232657647446656759257)
  ·
    refine ⟨99784674493235584992569443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133046232657647446656759257 99784674493235584992569443)
    ·
      refine ⟨149677011739853377488854165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99784674493235584992569443 149677011739853377488854165)
      ·
        refine ⟨7016109925305627069790039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149677011739853377488854165 7016109925305627069790039)
        ·
          refine ⟨10524164887958440604685059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7016109925305627069790039 10524164887958440604685059)
          ·
            refine ⟨15786247331937660907027589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10524164887958440604685059 15786247331937660907027589)
            ·
              refine ⟨2959921374738311420067673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15786247331937660907027589 2959921374738311420067673)
              ·
                refine ⟨2219941031053733565050755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2959921374738311420067673 2219941031053733565050755)
                ·
                  refine ⟨3329911546580600347576133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2219941031053733565050755 3329911546580600347576133)
                  ·
                    refine ⟨624358414983862565170525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3329911546580600347576133 624358414983862565170525)
                    ·
                      rfl

theorem cell23_3647801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 1, 4].length) (baseStart_3647801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647801 prefixEnd_3647801 := by exact prefixLift 3647801
  have htrace : WordTrace (prefixWord ++ tailWord_3647801) baseStart_3647801 baseEnd_3647801 := by
    simpa [prefixWord, tailWord_3647801, baseEnd_3647801] using wordTrace_append hprefix tailTrace_3647801
  have hstable : (prefixWord ++ tailWord_3647801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647801).length < 2 ^ (prefixWord ++ tailWord_3647801).sum := by decide
  have hdescent : baseEnd_3647801 < baseStart_3647801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647807 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 3, 1, 3]
def baseStart_3647807 : Nat := 118140960795 + 3647807 * 2 ^ 59
def prefixEnd_3647807 : Nat := 4983230072969 + 3 ^ 40 * 3647807 * 2
def baseEnd_3647807 : Nat := 1873078325835514672036547

theorem tailTrace_3647807 : CollatzResearch.WordTrace tailWord_3647807 prefixEnd_3647807 1873078325835514672036547 := by
  unfold tailWord_3647807
  simp only [CollatzResearch.WordTrace]
  refine ⟨133046451495625709681477675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88697634330417139787651783 133046451495625709681477675)
  ·
    refine ⟨199569677243438564522216513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133046451495625709681477675 199569677243438564522216513)
    ·
      refine ⟨149677257932578923391662385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199569677243438564522216513 149677257932578923391662385)
      ·
        refine ⟨112257943449434192543746789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149677257932578923391662385 112257943449434192543746789)
        ·
          refine ⟨21048364396768911101952523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112257943449434192543746789 21048364396768911101952523)
          ·
            refine ⟨31572546595153366652928785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21048364396768911101952523 31572546595153366652928785)
            ·
              refine ⟨23679409946365024989696589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31572546595153366652928785 23679409946365024989696589)
              ·
                refine ⟨8879778729886884371136221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23679409946365024989696589 8879778729886884371136221)
                ·
                  refine ⟨3329917023707581639176083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8879778729886884371136221 3329917023707581639176083)
                  ·
                    refine ⟨4994875535561372458764125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3329917023707581639176083 4994875535561372458764125)
                    ·
                      refine ⟨1873078325835514672036547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4994875535561372458764125 1873078325835514672036547)
                      ·
                        rfl

theorem cell23_3647807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_3647807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647807 prefixEnd_3647807 := by exact prefixLift 3647807
  have htrace : WordTrace (prefixWord ++ tailWord_3647807) baseStart_3647807 baseEnd_3647807 := by
    simpa [prefixWord, tailWord_3647807, baseEnd_3647807] using wordTrace_append hprefix tailTrace_3647807
  have hstable : (prefixWord ++ tailWord_3647807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647807).length < 2 ^ (prefixWord ++ tailWord_3647807).sum := by decide
  have hdescent : baseEnd_3647807 < baseStart_3647807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647884 : List Nat := [2, 2, 1, 2, 1, 5, 2, 2, 1, 2, 3]
def baseStart_3647884 : Nat := 118140960795 + 3647884 * 2 ^ 59
def prefixEnd_3647884 : Nat := 4983230072969 + 3 ^ 40 * 3647884 * 2
def baseEnd_3647884 : Nat := 1873117863845910870773693

theorem tailTrace_3647884 : CollatzResearch.WordTrace tailWord_3647884 prefixEnd_3647884 1873117863845910870773693 := by
  unfold tailWord_3647884
  simp only [CollatzResearch.WordTrace]
  refine ⟨66524629958173375916015353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88699506610897834554687137 66524629958173375916015353)
  ·
    refine ⟨49893472468630031937011515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66524629958173375916015353 49893472468630031937011515)
    ·
      refine ⟨74840208702945047905517273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49893472468630031937011515 74840208702945047905517273)
      ·
        refine ⟨56130156527208785929137955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74840208702945047905517273 56130156527208785929137955)
        ·
          refine ⟨84195234790813178893706933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56130156527208785929137955 84195234790813178893706933)
          ·
            refine ⟨7893303261638735521285025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84195234790813178893706933 7893303261638735521285025)
            ·
              refine ⟨5919977446229051640963769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7893303261638735521285025 5919977446229051640963769)
              ·
                refine ⟨4439983084671788730722827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5919977446229051640963769 4439983084671788730722827)
                ·
                  refine ⟨6659974627007683096084241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4439983084671788730722827 6659974627007683096084241)
                  ·
                    refine ⟨4994980970255762322063181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6659974627007683096084241 4994980970255762322063181)
                    ·
                      refine ⟨1873117863845910870773693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4994980970255762322063181 1873117863845910870773693)
                      ·
                        rfl

theorem cell23_3647884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_3647884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647884 prefixEnd_3647884 := by exact prefixLift 3647884
  have htrace : WordTrace (prefixWord ++ tailWord_3647884) baseStart_3647884 baseEnd_3647884 := by
    simpa [prefixWord, tailWord_3647884, baseEnd_3647884] using wordTrace_append hprefix tailTrace_3647884
  have hstable : (prefixWord ++ tailWord_3647884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647884).length < 2 ^ (prefixWord ++ tailWord_3647884).sum := by decide
  have hdescent : baseEnd_3647884 < baseStart_3647884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647897 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 6, 1, 3]
def baseStart_3647897 : Nat := 118140960795 + 3647897 * 2 ^ 59
def prefixEnd_3647897 : Nat := 4983230072969 + 3 ^ 40 * 3647897 * 2
def baseEnd_3647897 : Nat := 1873124539094419319911133

theorem tailTrace_3647897 : CollatzResearch.WordTrace tailWord_3647897 prefixEnd_3647897 1873124539094419319911133 := by
  unfold tailWord_3647897
  simp only [CollatzResearch.WordTrace]
  refine ⟨133049734065299655052253945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88699822710199770034835963 133049734065299655052253945)
  ·
    refine ⟨99787300548974741289190459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133049734065299655052253945 99787300548974741289190459)
    ·
      refine ⟨149680950823462111933785689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99787300548974741289190459 149680950823462111933785689)
      ·
        refine ⟨112260713117596583950339267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149680950823462111933785689 112260713117596583950339267)
        ·
          refine ⟨168391069676394875925508901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112260713117596583950339267 168391069676394875925508901)
          ·
            refine ⟨31573325564324039236032919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168391069676394875925508901 31573325564324039236032919)
            ·
              refine ⟨47359988346486058854049379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31573325564324039236032919 47359988346486058854049379)
              ·
                refine ⟨71039982519729088281074069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47359988346486058854049379 71039982519729088281074069)
                ·
                  refine ⟨3329999180612301013175347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71039982519729088281074069 3329999180612301013175347)
                  ·
                    refine ⟨4994998770918451519763021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3329999180612301013175347 4994998770918451519763021)
                    ·
                      refine ⟨1873124539094419319911133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4994998770918451519763021 1873124539094419319911133)
                      ·
                        rfl

theorem cell23_3647897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_3647897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647897 prefixEnd_3647897 := by exact prefixLift 3647897
  have htrace : WordTrace (prefixWord ++ tailWord_3647897) baseStart_3647897 baseEnd_3647897 := by
    simpa [prefixWord, tailWord_3647897, baseEnd_3647897] using wordTrace_append hprefix tailTrace_3647897
  have hstable : (prefixWord ++ tailWord_3647897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647897).length < 2 ^ (prefixWord ++ tailWord_3647897).sum := by decide
  have hdescent : baseEnd_3647897 < baseStart_3647897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647898 : List Nat := [3, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2]
def baseStart_3647898 : Nat := 118140960795 + 3647898 * 2 ^ 59
def prefixEnd_3647898 : Nat := 4983230072969 + 3 ^ 40 * 3647898 * 2
def baseEnd_3647898 : Nat := 1873125052575073815998629

theorem tailTrace_3647898 : CollatzResearch.WordTrace tailWord_3647898 prefixEnd_3647898 1873125052575073815998629 := by
  unfold tailWord_3647898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33262442634574008055760087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88699847025530688148693565 33262442634574008055760087)
  ·
    refine ⟨49893663951861012083640131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33262442634574008055760087 49893663951861012083640131)
    ·
      refine ⟨74840495927791518125460197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49893663951861012083640131 74840495927791518125460197)
      ·
        refine ⟨14032592986460909648523787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74840495927791518125460197 14032592986460909648523787)
        ·
          refine ⟨21048889479691364472785681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14032592986460909648523787 21048889479691364472785681)
          ·
            refine ⟨15786667109768523354589261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21048889479691364472785681 15786667109768523354589261)
            ·
              refine ⟨5920000166163196257970973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15786667109768523354589261 5920000166163196257970973)
              ·
                refine ⟨2220000062311198596739115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5920000166163196257970973 2220000062311198596739115)
                ·
                  refine ⟨3330000093466797895108673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2220000062311198596739115 3330000093466797895108673)
                  ·
                    refine ⟨2497500070100098421331505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3330000093466797895108673 2497500070100098421331505)
                    ·
                      refine ⟨1873125052575073815998629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2497500070100098421331505 1873125052575073815998629)
                      ·
                        rfl

theorem cell23_3647898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_3647898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647898 prefixEnd_3647898 := by exact prefixLift 3647898
  have htrace : WordTrace (prefixWord ++ tailWord_3647898) baseStart_3647898 baseEnd_3647898 := by
    simpa [prefixWord, tailWord_3647898, baseEnd_3647898] using wordTrace_append hprefix tailTrace_3647898
  have hstable : (prefixWord ++ tailWord_3647898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647898).length < 2 ^ (prefixWord ++ tailWord_3647898).sum := by decide
  have hdescent : baseEnd_3647898 < baseStart_3647898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647930 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 2, 6]
def baseStart_3647930 : Nat := 118140960795 + 3647930 * 2 ^ 59
def prefixEnd_3647930 : Nat := 4983230072969 + 3 ^ 40 * 3647930 * 2
def baseEnd_3647930 : Nat := 624380494652005896932827

theorem tailTrace_3647930 : CollatzResearch.WordTrace tailWord_3647930 prefixEnd_3647930 624380494652005896932827 := by
  unfold tailWord_3647930
  simp only [CollatzResearch.WordTrace]
  refine ⟨33262734418545025422051311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88700625116120067792136829 33262734418545025422051311)
  ·
    refine ⟨49894101627817538133076967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33262734418545025422051311 49894101627817538133076967)
    ·
      refine ⟨74841152441726307199615451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49894101627817538133076967 74841152441726307199615451)
      ·
        refine ⟨112261728662589460799423177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74841152441726307199615451 112261728662589460799423177)
        ·
          refine ⟨84196296496942095599567383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112261728662589460799423177 84196296496942095599567383)
          ·
            refine ⟨126294444745413143399351075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84196296496942095599567383 126294444745413143399351075)
            ·
              refine ⟨189441667118119715099026613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126294444745413143399351075 189441667118119715099026613)
              ·
                refine ⟨17760156292323723290533745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189441667118119715099026613 17760156292323723290533745)
                ·
                  refine ⟨13320117219242792467900309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17760156292323723290533745 13320117219242792467900309)
                  ·
                    refine ⟨624380494652005896932827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13320117219242792467900309 624380494652005896932827)
                    ·
                      rfl

theorem cell23_3647930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_3647930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647930 prefixEnd_3647930 := by exact prefixLift 3647930
  have htrace : WordTrace (prefixWord ++ tailWord_3647930) baseStart_3647930 baseEnd_3647930 := by
    simpa [prefixWord, tailWord_3647930, baseEnd_3647930] using wordTrace_append hprefix tailTrace_3647930
  have hstable : (prefixWord ++ tailWord_3647930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647930).length < 2 ^ (prefixWord ++ tailWord_3647930).sum := by decide
  have hdescent : baseEnd_3647930 < baseStart_3647930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647957 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_3647957 : Nat := 118140960795 + 3647957 * 2 ^ 59
def prefixEnd_3647957 : Nat := 4983230072969 + 3 ^ 40 * 3647957 * 2
def baseEnd_3647957 : Nat := 1873155347933689085160857

theorem tailTrace_3647957 : CollatzResearch.WordTrace tailWord_3647957 prefixEnd_3647957 1873155347933689085160857 := by
  unfold tailWord_3647957
  simp only [CollatzResearch.WordTrace]
  refine ⟨133051922445082285299438125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88701281630054856866292083 133051922445082285299438125)
  ·
    refine ⟨49894470916905856987289297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133051922445082285299438125 49894470916905856987289297)
    ·
      refine ⟨37420853187679392740466973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49894470916905856987289297 37420853187679392740466973)
      ·
        refine ⟨14032819945379772277675115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37420853187679392740466973 14032819945379772277675115)
        ·
          refine ⟨21049229918069658416512673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14032819945379772277675115 21049229918069658416512673)
          ·
            refine ⟨15786922438552243812384505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21049229918069658416512673 15786922438552243812384505)
            ·
              refine ⟨11840191828914182859288379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15786922438552243812384505 11840191828914182859288379)
              ·
                refine ⟨17760287743371274288932569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11840191828914182859288379 17760287743371274288932569)
                ·
                  refine ⟨13320215807528455716699427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17760287743371274288932569 13320215807528455716699427)
                  ·
                    refine ⟨19980323711292683575049141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13320215807528455716699427 19980323711292683575049141)
                    ·
                      refine ⟨1873155347933689085160857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19980323711292683575049141 1873155347933689085160857)
                      ·
                        rfl

theorem cell23_3647957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_3647957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647957 prefixEnd_3647957 := by exact prefixLift 3647957
  have htrace : WordTrace (prefixWord ++ tailWord_3647957) baseStart_3647957 baseEnd_3647957 := by
    simpa [prefixWord, tailWord_3647957, baseEnd_3647957] using wordTrace_append hprefix tailTrace_3647957
  have hstable : (prefixWord ++ tailWord_3647957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647957).length < 2 ^ (prefixWord ++ tailWord_3647957).sum := by decide
  have hdescent : baseEnd_3647957 < baseStart_3647957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3647987 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 3]
def baseStart_3647987 : Nat := 118140960795 + 3647987 * 2 ^ 59
def prefixEnd_3647987 : Nat := 4983230072969 + 3 ^ 40 * 3647987 * 2
def baseEnd_3647987 : Nat := 1873170752353323967785719

theorem tailTrace_3647987 : CollatzResearch.WordTrace tailWord_3647987 prefixEnd_3647987 1873170752353323967785719 := by
  unfold tailWord_3647987
  simp only [CollatzResearch.WordTrace]
  refine ⟨133053016634973600423030215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88702011089982400282020143 133053016634973600423030215)
  ·
    refine ⟨199579524952460400634545323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133053016634973600423030215 199579524952460400634545323)
    ·
      refine ⟨299369287428690600951817985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199579524952460400634545323 299369287428690600951817985)
      ·
        refine ⟨224526965571517950713863489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299369287428690600951817985 224526965571517950713863489)
        ·
          refine ⟨168395224178638463035397617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224526965571517950713863489 168395224178638463035397617)
          ·
            refine ⟨126296418133978847276548213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168395224178638463035397617 126296418133978847276548213)
            ·
              refine ⟨11840289200060516932176395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126296418133978847276548213 11840289200060516932176395)
              ·
                refine ⟨17760433800090775398264593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11840289200060516932176395 17760433800090775398264593)
                ·
                  refine ⟨13320325350068081548698445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17760433800090775398264593 13320325350068081548698445)
                  ·
                    refine ⟨4995122006275530580761917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13320325350068081548698445 4995122006275530580761917)
                    ·
                      refine ⟨1873170752353323967785719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4995122006275530580761917 1873170752353323967785719)
                      ·
                        rfl

theorem cell23_3647987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 3].length) (baseStart_3647987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3647987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3647987 prefixEnd_3647987 := by exact prefixLift 3647987
  have htrace : WordTrace (prefixWord ++ tailWord_3647987) baseStart_3647987 baseEnd_3647987 := by
    simpa [prefixWord, tailWord_3647987, baseEnd_3647987] using wordTrace_append hprefix tailTrace_3647987
  have hstable : (prefixWord ++ tailWord_3647987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3647987).length < 2 ^ (prefixWord ++ tailWord_3647987).sum := by decide
  have hdescent : baseEnd_3647987 < baseStart_3647987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3647987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648000 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 5]
def baseStart_3648000 : Nat := 118140960795 + 3648000 * 2 ^ 59
def prefixEnd_3648000 : Nat := 4983230072969 + 3 ^ 40 * 3648000 * 2
def baseEnd_3648000 : Nat := 1873177427601832416923159

theorem tailTrace_3648000 : CollatzResearch.WordTrace tailWord_3648000 prefixEnd_3648000 1873177427601832416923159 := by
  unfold tailWord_3648000
  simp only [CollatzResearch.WordTrace]
  refine ⟨66526745391963251821626727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88702327189284335762168969 66526745391963251821626727)
  ·
    refine ⟨99790118087944877732440091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66526745391963251821626727 99790118087944877732440091)
    ·
      refine ⟨149685177131917316598660137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99790118087944877732440091 149685177131917316598660137)
      ·
        refine ⟨112263882848937987448995103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149685177131917316598660137 112263882848937987448995103)
        ·
          refine ⟨168395824273406981173492655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112263882848937987448995103 168395824273406981173492655)
          ·
            refine ⟨252593736410110471760238983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168395824273406981173492655 252593736410110471760238983)
            ·
              refine ⟨378890604615165707640358475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252593736410110471760238983 378890604615165707640358475)
              ·
                refine ⟨568335906922748561460537713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378890604615165707640358475 568335906922748561460537713)
                ·
                  refine ⟨426251930192061421095403285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568335906922748561460537713 426251930192061421095403285)
                  ·
                    refine ⟨19980559227752879113847029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 426251930192061421095403285 19980559227752879113847029)
                    ·
                      refine ⟨1873177427601832416923159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19980559227752879113847029 1873177427601832416923159)
                      ·
                        rfl

theorem cell23_3648000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_3648000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648000 prefixEnd_3648000 := by exact prefixLift 3648000
  have htrace : WordTrace (prefixWord ++ tailWord_3648000) baseStart_3648000 baseEnd_3648000 := by
    simpa [prefixWord, tailWord_3648000, baseEnd_3648000] using wordTrace_append hprefix tailTrace_3648000
  have hstable : (prefixWord ++ tailWord_3648000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648000).length < 2 ^ (prefixWord ++ tailWord_3648000).sum := by decide
  have hdescent : baseEnd_3648000 < baseStart_3648000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648057 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3648057 : Nat := 118140960795 + 3648057 * 2 ^ 59
def prefixEnd_3648057 : Nat := 4983230072969 + 3 ^ 40 * 3648057 * 2
def baseEnd_3648057 : Nat := 1873206695999138693910397

theorem tailTrace_3648057 : CollatzResearch.WordTrace tailWord_3648057 prefixEnd_3648057 1873206695999138693910397 := by
  unfold tailWord_3648057
  simp only [CollatzResearch.WordTrace]
  refine ⟨133055569744720002378078425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88703713163146668252052283 133055569744720002378078425)
  ·
    refine ⟨99791677308540001783558819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133055569744720002378078425 99791677308540001783558819)
    ·
      refine ⟨149687515962810002675338229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99791677308540001783558819 149687515962810002675338229)
      ·
        refine ⟨14033204621513437750812959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149687515962810002675338229 14033204621513437750812959)
        ·
          refine ⟨21049806932270156626219439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14033204621513437750812959 21049806932270156626219439)
          ·
            refine ⟨31574710398405234939329159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21049806932270156626219439 31574710398405234939329159)
            ·
              refine ⟨47362065597607852408993739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31574710398405234939329159 47362065597607852408993739)
              ·
                refine ⟨71043098396411778613490609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47362065597607852408993739 71043098396411778613490609)
                ·
                  refine ⟨53282323797308833960117957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71043098396411778613490609 53282323797308833960117957)
                  ·
                    refine ⟨9990435711995406367522117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53282323797308833960117957 9990435711995406367522117)
                    ·
                      refine ⟨1873206695999138693910397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9990435711995406367522117 1873206695999138693910397)
                      ·
                        rfl

theorem cell23_3648057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3648057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648057 prefixEnd_3648057 := by exact prefixLift 3648057
  have htrace : WordTrace (prefixWord ++ tailWord_3648057) baseStart_3648057 baseEnd_3648057 := by
    simpa [prefixWord, tailWord_3648057, baseEnd_3648057] using wordTrace_append hprefix tailTrace_3648057
  have hstable : (prefixWord ++ tailWord_3648057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648057).length < 2 ^ (prefixWord ++ tailWord_3648057).sum := by decide
  have hdescent : baseEnd_3648057 < baseStart_3648057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648121 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 2, 3, 2]
def baseStart_3648121 : Nat := 118140960795 + 3648121 * 2 ^ 59
def prefixEnd_3648121 : Nat := 4983230072969 + 3 ^ 40 * 3648121 * 2
def baseEnd_3648121 : Nat := 1873239558761026443510103

theorem tailTrace_3648121 : CollatzResearch.WordTrace tailWord_3648121 prefixEnd_3648121 1873239558761026443510103 := by
  unfold tailWord_3648121
  simp only [CollatzResearch.WordTrace]
  refine ⟨133057904016488141308408217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88705269344325427538938811 133057904016488141308408217)
  ·
    refine ⟨99793428012366105981306163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133057904016488141308408217 99793428012366105981306163)
    ·
      refine ⟨149690142018549158971959245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99793428012366105981306163 149690142018549158971959245)
      ·
        refine ⟨56133803256955934614484717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149690142018549158971959245 56133803256955934614484717)
        ·
          refine ⟨21050176221358475480431769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56133803256955934614484717 21050176221358475480431769)
          ·
            refine ⟨15787632166018856610323827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21050176221358475480431769 15787632166018856610323827)
            ·
              refine ⟨23681448249028284915485741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15787632166018856610323827 23681448249028284915485741)
              ·
                refine ⟨8880543093385606843307153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23681448249028284915485741 8880543093385606843307153)
                ·
                  refine ⟨6660407320039205132480365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8880543093385606843307153 6660407320039205132480365)
                  ·
                    refine ⟨2497652745014701924680137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6660407320039205132480365 2497652745014701924680137)
                    ·
                      refine ⟨1873239558761026443510103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2497652745014701924680137 1873239558761026443510103)
                      ·
                        rfl

theorem cell23_3648121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_3648121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648121 prefixEnd_3648121 := by exact prefixLift 3648121
  have htrace : WordTrace (prefixWord ++ tailWord_3648121) baseStart_3648121 baseEnd_3648121 := by
    simpa [prefixWord, tailWord_3648121, baseEnd_3648121] using wordTrace_append hprefix tailTrace_3648121
  have hstable : (prefixWord ++ tailWord_3648121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648121).length < 2 ^ (prefixWord ++ tailWord_3648121).sum := by decide
  have hdescent : baseEnd_3648121 < baseStart_3648121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648161 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 1, 6]
def baseStart_3648161 : Nat := 118140960795 + 3648161 * 2 ^ 59
def prefixEnd_3648161 : Nat := 4983230072969 + 3 ^ 40 * 3648161 * 2
def baseEnd_3648161 : Nat := 624420032662402095669973

theorem tailTrace_3648161 : CollatzResearch.WordTrace tailWord_3648161 prefixEnd_3648161 624420032662402095669973 := by
  unfold tailWord_3648161
  simp only [CollatzResearch.WordTrace]
  refine ⟨133059362936343228139864337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88706241957562152093242891 133059362936343228139864337)
  ·
    refine ⟨99794522202257421104898253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133059362936343228139864337 99794522202257421104898253)
    ·
      refine ⟨37422945825846532914336845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99794522202257421104898253 37422945825846532914336845)
      ·
        refine ⟨14033604684692449842876317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37422945825846532914336845 14033604684692449842876317)
        ·
          refine ⟨5262601756759668691078619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14033604684692449842876317 5262601756759668691078619)
          ·
            refine ⟨7893902635139503036617929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5262601756759668691078619 7893902635139503036617929)
            ·
              refine ⟨5920426976354627277463447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7893902635139503036617929 5920426976354627277463447)
              ·
                refine ⟨8880640464531940916195171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5920426976354627277463447 8880640464531940916195171)
                ·
                  refine ⟨13320960696797911374292757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8880640464531940916195171 13320960696797911374292757)
                  ·
                    refine ⟨624420032662402095669973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13320960696797911374292757 624420032662402095669973)
                    ·
                      rfl

theorem cell23_3648161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_3648161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648161 prefixEnd_3648161 := by exact prefixLift 3648161
  have htrace : WordTrace (prefixWord ++ tailWord_3648161) baseStart_3648161 baseEnd_3648161 := by
    simpa [prefixWord, tailWord_3648161, baseEnd_3648161] using wordTrace_append hprefix tailTrace_3648161
  have hstable : (prefixWord ++ tailWord_3648161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648161).length < 2 ^ (prefixWord ++ tailWord_3648161).sum := by decide
  have hdescent : baseEnd_3648161 < baseStart_3648161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648181 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3648181 : Nat := 118140960795 + 3648181 * 2 ^ 59
def prefixEnd_3648181 : Nat := 4983230072969 + 3 ^ 40 * 3648181 * 2
def baseEnd_3648181 : Nat := 1873270367600296208759827

theorem tailTrace_3648181 : CollatzResearch.WordTrace tailWord_3648181 prefixEnd_3648181 1873270367600296208759827 := by
  unfold tailWord_3648181
  simp only [CollatzResearch.WordTrace]
  refine ⟨133060092396270771555592397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88706728264180514370394931 133060092396270771555592397)
  ·
    refine ⟨49897534648601539333347149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133060092396270771555592397 49897534648601539333347149)
    ·
      refine ⟨18711575493225577250005181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49897534648601539333347149 18711575493225577250005181)
      ·
        refine ⟨7016840809959591468751943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18711575493225577250005181 7016840809959591468751943)
        ·
          refine ⟨10525261214939387203127915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7016840809959591468751943 10525261214939387203127915)
          ·
            refine ⟨15787891822409080804691873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10525261214939387203127915 15787891822409080804691873)
            ·
              refine ⟨11840918866806810603518905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15787891822409080804691873 11840918866806810603518905)
              ·
                refine ⟨8880689150105107952639179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11840918866806810603518905 8880689150105107952639179)
                ·
                  refine ⟨13321033725157661928958769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8880689150105107952639179 13321033725157661928958769)
                  ·
                    refine ⟨9990775293868246446719077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13321033725157661928958769 9990775293868246446719077)
                    ·
                      refine ⟨1873270367600296208759827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9990775293868246446719077 1873270367600296208759827)
                      ·
                        rfl

theorem cell23_3648181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3648181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648181 prefixEnd_3648181 := by exact prefixLift 3648181
  have htrace : WordTrace (prefixWord ++ tailWord_3648181) baseStart_3648181 baseEnd_3648181 := by
    simpa [prefixWord, tailWord_3648181, baseEnd_3648181] using wordTrace_append hprefix tailTrace_3648181
  have hstable : (prefixWord ++ tailWord_3648181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648181).length < 2 ^ (prefixWord ++ tailWord_3648181).sum := by decide
  have hdescent : baseEnd_3648181 < baseStart_3648181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648182 : List Nat := [5, 1, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_3648182 : Nat := 118140960795 + 3648182 * 2 ^ 59
def prefixEnd_3648182 : Nat := 4983230072969 + 3 ^ 40 * 3648182 * 2
def baseEnd_3648182 : Nat := 624423627026983568282441

theorem tailTrace_3648182 : CollatzResearch.WordTrace tailWord_3648182 prefixEnd_3648182 624423627026983568282441 := by
  unfold tailWord_3648182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8316258054329196795398675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88706752579511432484252533 8316258054329196795398675)
  ·
    refine ⟨12474387081493795193098013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8316258054329196795398675 12474387081493795193098013)
    ·
      refine ⟨4677895155560173197411755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12474387081493795193098013 4677895155560173197411755)
      ·
        refine ⟨7016842733340259796117633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4677895155560173197411755 7016842733340259796117633)
        ·
          refine ⟨5262632050005194847088225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7016842733340259796117633 5262632050005194847088225)
          ·
            refine ⟨3946974037503896135316169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5262632050005194847088225 3946974037503896135316169)
            ·
              refine ⟨2960230528127922101487127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3946974037503896135316169 2960230528127922101487127)
              ·
                refine ⟨4440345792191883152230691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2960230528127922101487127 4440345792191883152230691)
                ·
                  refine ⟨6660518688287824728346037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4440345792191883152230691 6660518688287824728346037)
                  ·
                    refine ⟨624423627026983568282441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6660518688287824728346037 624423627026983568282441)
                    ·
                      rfl

theorem cell23_3648182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_3648182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648182 prefixEnd_3648182 := by exact prefixLift 3648182
  have htrace : WordTrace (prefixWord ++ tailWord_3648182) baseStart_3648182 baseEnd_3648182 := by
    simpa [prefixWord, tailWord_3648182, baseEnd_3648182] using wordTrace_append hprefix tailTrace_3648182
  have hstable : (prefixWord ++ tailWord_3648182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648182).length < 2 ^ (prefixWord ++ tailWord_3648182).sum := by decide
  have hdescent : baseEnd_3648182 < baseStart_3648182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648197 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_3648197 : Nat := 118140960795 + 3648197 * 2 ^ 59
def prefixEnd_3648197 : Nat := 4983230072969 + 3 ^ 40 * 3648197 * 2
def baseEnd_3648197 : Nat := 1873278583290768146159753

theorem tailTrace_3648197 : CollatzResearch.WordTrace tailWord_3648197 prefixEnd_3648197 1873278583290768146159753 := by
  unfold tailWord_3648197
  simp only [CollatzResearch.WordTrace]
  refine ⟨133060675964212806288174845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88707117309475204192116563 133060675964212806288174845)
  ·
    refine ⟨49897753486579802358065567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133060675964212806288174845 49897753486579802358065567)
    ·
      refine ⟨74846630229869703537098351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49897753486579802358065567 74846630229869703537098351)
      ·
        refine ⟨112269945344804555305647527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74846630229869703537098351 112269945344804555305647527)
        ·
          refine ⟨168404918017206832958471291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112269945344804555305647527 168404918017206832958471291)
          ·
            refine ⟨252607377025810249437706937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168404918017206832958471291 252607377025810249437706937)
            ·
              refine ⟨189455532769357687078280203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252607377025810249437706937 189455532769357687078280203)
              ·
                refine ⟨284183299154036530617420305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189455532769357687078280203 284183299154036530617420305)
                ·
                  refine ⟨213137474365527397963065229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284183299154036530617420305 213137474365527397963065229)
                  ·
                    refine ⟨79926552887072774236149461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213137474365527397963065229 79926552887072774236149461)
                    ·
                      refine ⟨1873278583290768146159753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79926552887072774236149461 1873278583290768146159753)
                      ·
                        rfl

theorem cell23_3648197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_3648197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648197 prefixEnd_3648197 := by exact prefixLift 3648197
  have htrace : WordTrace (prefixWord ++ tailWord_3648197) baseStart_3648197 baseEnd_3648197 := by
    simpa [prefixWord, tailWord_3648197, baseEnd_3648197] using wordTrace_append hprefix tailTrace_3648197
  have hstable : (prefixWord ++ tailWord_3648197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648197).length < 2 ^ (prefixWord ++ tailWord_3648197).sum := by decide
  have hdescent : baseEnd_3648197 < baseStart_3648197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648228 : List Nat := [2, 3, 1, 1, 1, 4, 1, 4, 1, 3, 2]
def baseStart_3648228 : Nat := 118140960795 + 3648228 * 2 ^ 59
def prefixEnd_3648228 : Nat := 4983230072969 + 3 ^ 40 * 3648228 * 2
def baseEnd_3648228 : Nat := 1873294501191057524872111

theorem tailTrace_3648228 : CollatzResearch.WordTrace tailWord_3648228 prefixEnd_3648228 1873294501191057524872111 := by
  unfold tailWord_3648228
  simp only [CollatzResearch.WordTrace]
  refine ⟨66530903313550249291276669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88707871084733665721702225 66530903313550249291276669)
  ·
    refine ⟨24949088742581343484228751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66530903313550249291276669 24949088742581343484228751)
    ·
      refine ⟨37423633113872015226343127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24949088742581343484228751 37423633113872015226343127)
      ·
        refine ⟨56135449670808022839514691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37423633113872015226343127 56135449670808022839514691)
        ·
          refine ⟨84203174506212034259272037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56135449670808022839514691 84203174506212034259272037)
          ·
            refine ⟨15788095219914756423613507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84203174506212034259272037 15788095219914756423613507)
            ·
              refine ⟨23682142829872134635420261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15788095219914756423613507 23682142829872134635420261)
              ·
                refine ⟨4440401780601025244141299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23682142829872134635420261 4440401780601025244141299)
                ·
                  refine ⟨6660602670901537866211949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4440401780601025244141299 6660602670901537866211949)
                  ·
                    refine ⟨2497726001588076699829481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6660602670901537866211949 2497726001588076699829481)
                    ·
                      refine ⟨1873294501191057524872111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2497726001588076699829481 1873294501191057524872111)
                      ·
                        rfl

theorem cell23_3648228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_3648228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648228 prefixEnd_3648228 := by exact prefixLift 3648228
  have htrace : WordTrace (prefixWord ++ tailWord_3648228) baseStart_3648228 baseEnd_3648228 := by
    simpa [prefixWord, tailWord_3648228, baseEnd_3648228] using wordTrace_append hprefix tailTrace_3648228
  have hstable : (prefixWord ++ tailWord_3648228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648228).length < 2 ^ (prefixWord ++ tailWord_3648228).sum := by decide
  have hdescent : baseEnd_3648228 < baseStart_3648228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648241 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 3, 4, 2]
def baseStart_3648241 : Nat := 118140960795 + 3648241 * 2 ^ 59
def prefixEnd_3648241 : Nat := 4983230072969 + 3 ^ 40 * 3648241 * 2
def baseEnd_3648241 : Nat := 1873301176439565974009551

theorem tailTrace_3648241 : CollatzResearch.WordTrace tailWord_3648241 prefixEnd_3648241 1873301176439565974009551 := by
  unfold tailWord_3648241
  simp only [CollatzResearch.WordTrace]
  refine ⟨133062280776053401802776577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88708187184035601201851051 133062280776053401802776577)
  ·
    refine ⟨99796710582040051352082433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133062280776053401802776577 99796710582040051352082433)
    ·
      refine ⟨74847532936530038514061825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99796710582040051352082433 74847532936530038514061825)
      ·
        refine ⟨56135649702397528885546369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74847532936530038514061825 56135649702397528885546369)
        ·
          refine ⟨42101737276798146664159777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56135649702397528885546369 42101737276798146664159777)
          ·
            refine ⟨31576302957598609998119833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42101737276798146664159777 31576302957598609998119833)
            ·
              refine ⟨23682227218198957498589875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31576302957598609998119833 23682227218198957498589875)
              ·
                refine ⟨35523340827298436247884813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23682227218198957498589875 35523340827298436247884813)
                ·
                  refine ⟨13321252810236913592956805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35523340827298436247884813 13321252810236913592956805)
                  ·
                    refine ⟨2497734901919421298679401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13321252810236913592956805 2497734901919421298679401)
                    ·
                      refine ⟨1873301176439565974009551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2497734901919421298679401 1873301176439565974009551)
                      ·
                        rfl

theorem cell23_3648241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_3648241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648241 prefixEnd_3648241 := by exact prefixLift 3648241
  have htrace : WordTrace (prefixWord ++ tailWord_3648241) baseStart_3648241 baseEnd_3648241 := by
    simpa [prefixWord, tailWord_3648241, baseEnd_3648241] using wordTrace_append hprefix tailTrace_3648241
  have hstable : (prefixWord ++ tailWord_3648241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648241).length < 2 ^ (prefixWord ++ tailWord_3648241).sum := by decide
  have hdescent : baseEnd_3648241 < baseStart_3648241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648344 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_3648344 : Nat := 118140960795 + 3648344 * 2 ^ 59
def prefixEnd_3648344 : Nat := 4983230072969 + 3 ^ 40 * 3648344 * 2
def baseEnd_3648344 : Nat := 1873354064946979071021577

theorem tailTrace_3648344 : CollatzResearch.WordTrace tailWord_3648344 prefixEnd_3648344 1873354064946979071021577 := by
  unfold tailWord_3648344
  simp only [CollatzResearch.WordTrace]
  refine ⟨66533018747340125196888043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88710691663120166929184057 66533018747340125196888043)
  ·
    refine ⟨99799528121010187795332065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66533018747340125196888043 99799528121010187795332065)
    ·
      refine ⟨74849646090757640846499049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99799528121010187795332065 74849646090757640846499049)
      ·
        refine ⟨56137234568068230634874287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74849646090757640846499049 56137234568068230634874287)
        ·
          refine ⟨84205851852102345952311431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56137234568068230634874287 84205851852102345952311431)
          ·
            refine ⟨126308777778153518928467147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84205851852102345952311431 126308777778153518928467147)
            ·
              refine ⟨189463166667230278392700721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126308777778153518928467147 189463166667230278392700721)
              ·
                refine ⟨142097375000422708794525541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189463166667230278392700721 142097375000422708794525541)
                ·
                  refine ⟨26643257812579257898973539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142097375000422708794525541 26643257812579257898973539)
                  ·
                    refine ⟨39964886718868886848460309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26643257812579257898973539 39964886718868886848460309)
                    ·
                      refine ⟨1873354064946979071021577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39964886718868886848460309 1873354064946979071021577)
                      ·
                        rfl

theorem cell23_3648344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_3648344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648344 prefixEnd_3648344 := by exact prefixLift 3648344
  have htrace : WordTrace (prefixWord ++ tailWord_3648344) baseStart_3648344 baseEnd_3648344 := by
    simpa [prefixWord, tailWord_3648344, baseEnd_3648344] using wordTrace_append hprefix tailTrace_3648344
  have hstable : (prefixWord ++ tailWord_3648344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648344).length < 2 ^ (prefixWord ++ tailWord_3648344).sum := by decide
  have hdescent : baseEnd_3648344 < baseStart_3648344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648348 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3648348 : Nat := 118140960795 + 3648348 * 2 ^ 59
def prefixEnd_3648348 : Nat := 4983230072969 + 3 ^ 40 * 3648348 * 2
def baseEnd_3648348 : Nat := 1873356118869597055371559

theorem tailTrace_3648348 : CollatzResearch.WordTrace tailWord_3648348 prefixEnd_3648348 1873356118869597055371559 := by
  unfold tailWord_3648348
  simp only [CollatzResearch.WordTrace]
  refine ⟨66533091693332879538460849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88710788924443839384614465 66533091693332879538460849)
  ·
    refine ⟨49899818769999659653845637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66533091693332879538460849 49899818769999659653845637)
    ·
      refine ⟨9356216019374936185096057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49899818769999659653845637 9356216019374936185096057)
      ·
        refine ⟨7017162014531202138822043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9356216019374936185096057 7017162014531202138822043)
        ·
          refine ⟨10525743021796803208233065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7017162014531202138822043 10525743021796803208233065)
          ·
            refine ⟨7894307266347602406174799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10525743021796803208233065 7894307266347602406174799)
            ·
              refine ⟨11841460899521403609262199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7894307266347602406174799 11841460899521403609262199)
              ·
                refine ⟨17762191349282105413893299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11841460899521403609262199 17762191349282105413893299)
                ·
                  refine ⟨26643287023923158120839949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17762191349282105413893299 26643287023923158120839949)
                  ·
                    refine ⟨9991232633971184295314981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26643287023923158120839949 9991232633971184295314981)
                    ·
                      refine ⟨1873356118869597055371559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9991232633971184295314981 1873356118869597055371559)
                      ·
                        rfl

theorem cell23_3648348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3648348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648348 prefixEnd_3648348 := by exact prefixLift 3648348
  have htrace : WordTrace (prefixWord ++ tailWord_3648348) baseStart_3648348 baseEnd_3648348 := by
    simpa [prefixWord, tailWord_3648348, baseEnd_3648348] using wordTrace_append hprefix tailTrace_3648348
  have hstable : (prefixWord ++ tailWord_3648348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648348).length < 2 ^ (prefixWord ++ tailWord_3648348).sum := by decide
  have hdescent : baseEnd_3648348 < baseStart_3648348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648351 : List Nat := [1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 3]
def baseStart_3648351 : Nat := 118140960795 + 3648351 * 2 ^ 59
def prefixEnd_3648351 : Nat := 4983230072969 + 3 ^ 40 * 3648351 * 2
def baseEnd_3648351 : Nat := 1873357659311560543634045

theorem tailTrace_3648351 : CollatzResearch.WordTrace tailWord_3648351 prefixEnd_3648351 1873357659311560543634045 := by
  unfold tailWord_3648351
  simp only [CollatzResearch.WordTrace]
  refine ⟨133066292805654890589280907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88710861870436593726187271 133066292805654890589280907)
  ·
    refine ⟨199599439208482335883921361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133066292805654890589280907 199599439208482335883921361)
    ·
      refine ⟨149699579406361751912941021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199599439208482335883921361 149699579406361751912941021)
      ·
        refine ⟨56137342277385656967352883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149699579406361751912941021 56137342277385656967352883)
        ·
          refine ⟨84206013416078485451029325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56137342277385656967352883 84206013416078485451029325)
          ·
            refine ⟨31577255031029432044135997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84206013416078485451029325 31577255031029432044135997)
            ·
              refine ⟨11841470636636037016550999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31577255031029432044135997 11841470636636037016550999)
              ·
                refine ⟨17762205954954055524826499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11841470636636037016550999 17762205954954055524826499)
                ·
                  refine ⟨26643308932431083287239749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17762205954954055524826499 26643308932431083287239749)
                  ·
                    refine ⟨4995620424830828116357453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26643308932431083287239749 4995620424830828116357453)
                    ·
                      refine ⟨1873357659311560543634045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4995620424830828116357453 1873357659311560543634045)
                      ·
                        rfl

theorem cell23_3648351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_3648351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648351 prefixEnd_3648351 := by exact prefixLift 3648351
  have htrace : WordTrace (prefixWord ++ tailWord_3648351) baseStart_3648351 baseEnd_3648351 := by
    simpa [prefixWord, tailWord_3648351, baseEnd_3648351] using wordTrace_append hprefix tailTrace_3648351
  have hstable : (prefixWord ++ tailWord_3648351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648351).length < 2 ^ (prefixWord ++ tailWord_3648351).sum := by decide
  have hdescent : baseEnd_3648351 < baseStart_3648351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648371 : List Nat := [1, 1, 1, 2, 2, 1, 7, 2, 6]
def baseStart_3648371 : Nat := 118140960795 + 3648371 * 2 ^ 59
def prefixEnd_3648371 : Nat := 4983230072969 + 3 ^ 40 * 3648371 * 2
def baseEnd_3648371 : Nat := 208151992102738940598217

theorem tailTrace_3648371 : CollatzResearch.WordTrace tailWord_3648371 prefixEnd_3648371 208151992102738940598217 := by
  unfold tailWord_3648371
  simp only [CollatzResearch.WordTrace]
  refine ⟨133067022265582434005008967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88711348177054956003339311 133067022265582434005008967)
  ·
    refine ⟨199600533398373651007513451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133067022265582434005008967 199600533398373651007513451)
    ·
      refine ⟨299400800097560476511270177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199600533398373651007513451 299400800097560476511270177)
      ·
        refine ⟨224550600073170357383452633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299400800097560476511270177 224550600073170357383452633)
        ·
          refine ⟨168412950054877768037589475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224550600073170357383452633 168412950054877768037589475)
          ·
            refine ⟨252619425082316652056384213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168412950054877768037589475 252619425082316652056384213)
            ·
              refine ⟨5920767775366796532571505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 252619425082316652056384213 5920767775366796532571505)
              ·
                refine ⟨4440575831525097399428629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5920767775366796532571505 4440575831525097399428629)
                ·
                  refine ⟨208151992102738940598217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4440575831525097399428629 208151992102738940598217)
                  ·
                    rfl

theorem cell23_3648371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 6].length) (baseStart_3648371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648371 prefixEnd_3648371 := by exact prefixLift 3648371
  have htrace : WordTrace (prefixWord ++ tailWord_3648371) baseStart_3648371 baseEnd_3648371 := by
    simpa [prefixWord, tailWord_3648371, baseEnd_3648371] using wordTrace_append hprefix tailTrace_3648371
  have hstable : (prefixWord ++ tailWord_3648371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648371).length < 2 ^ (prefixWord ++ tailWord_3648371).sum := by decide
  have hdescent : baseEnd_3648371 < baseStart_3648371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648384 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 2, 9]
def baseStart_3648384 : Nat := 118140960795 + 3648384 * 2 ^ 59
def prefixEnd_3648384 : Nat := 4983230072969 + 3 ^ 40 * 3648384 * 2
def baseEnd_3648384 : Nat := 624458201391052971507131

theorem tailTrace_3648384 : CollatzResearch.WordTrace tailWord_3648384 prefixEnd_3648384 624458201391052971507131 := by
  unfold tailWord_3648384
  simp only [CollatzResearch.WordTrace]
  refine ⟨66533748207267668612616103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88711664276356891483488137 66533748207267668612616103)
  ·
    refine ⟨99800622310901502918924155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66533748207267668612616103 99800622310901502918924155)
    ·
      refine ⟨149700933466352254378386233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99800622310901502918924155 149700933466352254378386233)
      ·
        refine ⟨112275700099764190783789675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149700933466352254378386233 112275700099764190783789675)
        ·
          refine ⟨168413550149646286175684513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112275700099764190783789675 168413550149646286175684513)
          ·
            refine ⟨126310162612234714631763385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168413550149646286175684513 126310162612234714631763385)
            ·
              refine ⟨94732621959176035973822539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126310162612234714631763385 94732621959176035973822539)
              ·
                refine ⟨142098932938764053960733809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94732621959176035973822539 142098932938764053960733809)
                ·
                  refine ⟨106574199704073040470550357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142098932938764053960733809 106574199704073040470550357)
                  ·
                    refine ⟨624458201391052971507131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 106574199704073040470550357 624458201391052971507131)
                    ·
                      rfl

theorem cell23_3648384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 9].length) (baseStart_3648384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648384 prefixEnd_3648384 := by exact prefixLift 3648384
  have htrace : WordTrace (prefixWord ++ tailWord_3648384) baseStart_3648384 baseEnd_3648384 := by
    simpa [prefixWord, tailWord_3648384, baseEnd_3648384] using wordTrace_append hprefix tailTrace_3648384
  have hstable : (prefixWord ++ tailWord_3648384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648384).length < 2 ^ (prefixWord ++ tailWord_3648384).sum := by decide
  have hdescent : baseEnd_3648384 < baseStart_3648384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648421 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_3648421 : Nat := 118140960795 + 3648421 * 2 ^ 59
def prefixEnd_3648421 : Nat := 4983230072969 + 3 ^ 40 * 3648421 * 2
def baseEnd_3648421 : Nat := 1873393602957375269758723

theorem tailTrace_3648421 : CollatzResearch.WordTrace tailWord_3648421 prefixEnd_3648421 1873393602957375269758723 := by
  unfold tailWord_3648421
  simp only [CollatzResearch.WordTrace]
  refine ⟨133068845915401292544329117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88712563943600861696219411 133068845915401292544329117)
  ·
    refine ⟨49900817218275484704123419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133068845915401292544329117 49900817218275484704123419)
    ·
      refine ⟨74851225827413227056185129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49900817218275484704123419 74851225827413227056185129)
      ·
        refine ⟨56138419370559920292138847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74851225827413227056185129 56138419370559920292138847)
        ·
          refine ⟨84207629055839880438208271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56138419370559920292138847 84207629055839880438208271)
          ·
            refine ⟨126311443583759820657312407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84207629055839880438208271 126311443583759820657312407)
            ·
              refine ⟨189467165375639730985968611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126311443583759820657312407 189467165375639730985968611)
              ·
                refine ⟨284200748063459596478952917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189467165375639730985968611 284200748063459596478952917)
                ·
                  refine ⟨6660955032737334292475459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 284200748063459596478952917 6660955032737334292475459)
                  ·
                    refine ⟨9991432549106001438713189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6660955032737334292475459 9991432549106001438713189)
                    ·
                      refine ⟨1873393602957375269758723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9991432549106001438713189 1873393602957375269758723)
                      ·
                        rfl

theorem cell23_3648421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_3648421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648421 prefixEnd_3648421 := by exact prefixLift 3648421
  have htrace : WordTrace (prefixWord ++ tailWord_3648421) baseStart_3648421 baseEnd_3648421 := by
    simpa [prefixWord, tailWord_3648421, baseEnd_3648421] using wordTrace_append hprefix tailTrace_3648421
  have hstable : (prefixWord ++ tailWord_3648421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648421).length < 2 ^ (prefixWord ++ tailWord_3648421).sum := by decide
  have hdescent : baseEnd_3648421 < baseStart_3648421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648455 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 3, 2, 2]
def baseStart_3648455 : Nat := 118140960795 + 3648455 * 2 ^ 59
def prefixEnd_3648455 : Nat := 4983230072969 + 3 ^ 40 * 3648455 * 2
def baseEnd_3648455 : Nat := 1873411061299628136733567

theorem tailTrace_3648455 : CollatzResearch.WordTrace tailWord_3648455 prefixEnd_3648455 1873411061299628136733567 := by
  unfold tailWord_3648455
  simp only [CollatzResearch.WordTrace]
  refine ⟨133070085997278116351066819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88713390664852077567377879 133070085997278116351066819)
  ·
    refine ⟨199605128995917174526600229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133070085997278116351066819 199605128995917174526600229)
    ·
      refine ⟨37425961686734470223737543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199605128995917174526600229 37425961686734470223737543)
      ·
        refine ⟨56138942530101705335606315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37425961686734470223737543 56138942530101705335606315)
        ·
          refine ⟨84208413795152558003409473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56138942530101705335606315 84208413795152558003409473)
          ·
            refine ⟨63156310346364418502557105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84208413795152558003409473 63156310346364418502557105)
            ·
              refine ⟨47367232759773313876917829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63156310346364418502557105 47367232759773313876917829)
              ·
                refine ⟨8881356142457496351922093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47367232759773313876917829 8881356142457496351922093)
                ·
                  refine ⟨3330508553421561131970785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8881356142457496351922093 3330508553421561131970785)
                  ·
                    refine ⟨2497881415066170848978089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3330508553421561131970785 2497881415066170848978089)
                    ·
                      refine ⟨1873411061299628136733567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2497881415066170848978089 1873411061299628136733567)
                      ·
                        rfl

theorem cell23_3648455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_3648455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648455 prefixEnd_3648455 := by exact prefixLift 3648455
  have htrace : WordTrace (prefixWord ++ tailWord_3648455) baseStart_3648455 baseEnd_3648455 := by
    simpa [prefixWord, tailWord_3648455, baseEnd_3648455] using wordTrace_append hprefix tailTrace_3648455
  have hstable : (prefixWord ++ tailWord_3648455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648455).length < 2 ^ (prefixWord ++ tailWord_3648455).sum := by decide
  have hdescent : baseEnd_3648455 < baseStart_3648455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648468 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3648468 : Nat := 118140960795 + 3648468 * 2 ^ 59
def prefixEnd_3648468 : Nat := 4983230072969 + 3 ^ 40 * 3648468 * 2
def baseEnd_3648468 : Nat := 1873417736548136585871007

theorem tailTrace_3648468 : CollatzResearch.WordTrace tailWord_3648468 prefixEnd_3648468 1873417736548136585871007 := by
  unfold tailWord_3648468
  simp only [CollatzResearch.WordTrace]
  refine ⟨66535280073115509785645029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88713706764154013047526705 66535280073115509785645029)
  ·
    refine ⟨12475365013709158084808443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66535280073115509785645029 12475365013709158084808443)
    ·
      refine ⟨18713047520563737127212665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12475365013709158084808443 18713047520563737127212665)
      ·
        refine ⟨14034785640422802845409499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18713047520563737127212665 14034785640422802845409499)
        ·
          refine ⟨21052178460634204268114249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14034785640422802845409499 21052178460634204268114249)
          ·
            refine ⟨15789133845475653201085687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21052178460634204268114249 15789133845475653201085687)
            ·
              refine ⟨23683700768213479801628531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15789133845475653201085687 23683700768213479801628531)
              ·
                refine ⟨35525551152320219702442797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23683700768213479801628531 35525551152320219702442797)
                ·
                  refine ⟨13322081682120082388416049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35525551152320219702442797 13322081682120082388416049)
                  ·
                    refine ⟨9991561261590061791312037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13322081682120082388416049 9991561261590061791312037)
                    ·
                      refine ⟨1873417736548136585871007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9991561261590061791312037 1873417736548136585871007)
                      ·
                        rfl

theorem cell23_3648468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3648468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648468 prefixEnd_3648468 := by exact prefixLift 3648468
  have htrace : WordTrace (prefixWord ++ tailWord_3648468) baseStart_3648468 baseEnd_3648468 := by
    simpa [prefixWord, tailWord_3648468, baseEnd_3648468] using wordTrace_append hprefix tailTrace_3648468
  have hstable : (prefixWord ++ tailWord_3648468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648468).length < 2 ^ (prefixWord ++ tailWord_3648468).sum := by decide
  have hdescent : baseEnd_3648468 < baseStart_3648468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648482 : List Nat := [3, 3, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3648482 : Nat := 118140960795 + 3648482 * 2 ^ 59
def prefixEnd_3648482 : Nat := 4983230072969 + 3 ^ 40 * 3648482 * 2
def baseEnd_3648482 : Nat := 624474975092433177031981

theorem tailTrace_3648482 : CollatzResearch.WordTrace tailWord_3648482 prefixEnd_3648482 624474975092433177031981 := by
  unfold tailWord_3648482
  simp only [CollatzResearch.WordTrace]
  refine ⟨33267767692045074990574925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88714047178786866641533133 33267767692045074990574925)
  ·
    refine ⟨12475412884516903121465597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33267767692045074990574925 12475412884516903121465597)
    ·
      refine ⟨4678279831693838670549599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12475412884516903121465597 4678279831693838670549599)
      ·
        refine ⟨7017419747540758005824399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4678279831693838670549599 7017419747540758005824399)
        ·
          refine ⟨10526129621311137008736599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7017419747540758005824399 10526129621311137008736599)
          ·
            refine ⟨15789194431966705513104899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10526129621311137008736599 15789194431966705513104899)
            ·
              refine ⟨23683791647950058269657349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15789194431966705513104899 23683791647950058269657349)
              ·
                refine ⟨4440710933990635925560753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23683791647950058269657349 4440710933990635925560753)
                ·
                  refine ⟨3330533200492976944170565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4440710933990635925560753 3330533200492976944170565)
                  ·
                    refine ⟨624474975092433177031981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3330533200492976944170565 624474975092433177031981)
                    ·
                      rfl

theorem cell23_3648482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3648482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648482 prefixEnd_3648482 := by exact prefixLift 3648482
  have htrace : WordTrace (prefixWord ++ tailWord_3648482) baseStart_3648482 baseEnd_3648482 := by
    simpa [prefixWord, tailWord_3648482, baseEnd_3648482] using wordTrace_append hprefix tailTrace_3648482
  have hstable : (prefixWord ++ tailWord_3648482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648482).length < 2 ^ (prefixWord ++ tailWord_3648482).sum := by decide
  have hdescent : baseEnd_3648482 < baseStart_3648482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648505 : List Nat := [1, 2, 1, 3, 1, 3, 1, 5, 2, 1, 3]
def baseStart_3648505 : Nat := 118140960795 + 3648505 * 2 ^ 59
def prefixEnd_3648505 : Nat := 4983230072969 + 3 ^ 40 * 3648505 * 2
def baseEnd_3648505 : Nat := 1873436735332352941108337

theorem tailTrace_3648505 : CollatzResearch.WordTrace tailWord_3648505 prefixEnd_3648505 1873436735332352941108337 := by
  unfold tailWord_3648505
  simp only [CollatzResearch.WordTrace]
  refine ⟨133071909647096974890386969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88714606431397983260257979 133071909647096974890386969)
  ·
    refine ⟨99803932235322731167790227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133071909647096974890386969 99803932235322731167790227)
    ·
      refine ⟨149705898352984096751685341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99803932235322731167790227 149705898352984096751685341)
      ·
        refine ⟨56139711882369036281882003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149705898352984096751685341 56139711882369036281882003)
        ·
          refine ⟨84209567823553554422823005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56139711882369036281882003 84209567823553554422823005)
          ·
            refine ⟨31578587933832582908558627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84209567823553554422823005 31578587933832582908558627)
            ·
              refine ⟨47367881900748874362837941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31578587933832582908558627 47367881900748874362837941)
              ·
                refine ⟨4440738928195206971516057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47367881900748874362837941 4440738928195206971516057)
                ·
                  refine ⟨3330554196146405228637043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4440738928195206971516057 3330554196146405228637043)
                  ·
                    refine ⟨4995831294219607842955565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3330554196146405228637043 4995831294219607842955565)
                    ·
                      refine ⟨1873436735332352941108337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4995831294219607842955565 1873436735332352941108337)
                      ·
                        rfl

theorem cell23_3648505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_3648505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648505 prefixEnd_3648505 := by exact prefixLift 3648505
  have htrace : WordTrace (prefixWord ++ tailWord_3648505) baseStart_3648505 baseEnd_3648505 := by
    simpa [prefixWord, tailWord_3648505, baseEnd_3648505] using wordTrace_append hprefix tailTrace_3648505
  have hstable : (prefixWord ++ tailWord_3648505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648505).length < 2 ^ (prefixWord ++ tailWord_3648505).sum := by decide
  have hdescent : baseEnd_3648505 < baseStart_3648505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648531 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 5]
def baseStart_3648531 : Nat := 118140960795 + 3648531 * 2 ^ 59
def prefixEnd_3648531 : Nat := 4983230072969 + 3 ^ 40 * 3648531 * 2
def baseEnd_3648531 : Nat := 1873450085829369839383217

theorem tailTrace_3648531 : CollatzResearch.WordTrace tailWord_3648531 prefixEnd_3648531 1873450085829369839383217 := by
  unfold tailWord_3648531
  simp only [CollatzResearch.WordTrace]
  refine ⟨133072857945002781330833447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88715238630001854220555631 133072857945002781330833447)
  ·
    refine ⟨199609286917504171996250171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133072857945002781330833447 199609286917504171996250171)
    ·
      refine ⟨299413930376256257994375257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199609286917504171996250171 299413930376256257994375257)
      ·
        refine ⟨224560447782192193495781443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299413930376256257994375257 224560447782192193495781443)
        ·
          refine ⟨336840671673288290243672165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224560447782192193495781443 336840671673288290243672165)
          ·
            refine ⟨63157625938741554420688531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 336840671673288290243672165 63157625938741554420688531)
            ·
              refine ⟨94736438908112331631032797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63157625938741554420688531 94736438908112331631032797)
              ·
                refine ⟨35526164590542124361637299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94736438908112331631032797 35526164590542124361637299)
                ·
                  refine ⟨53289246885813186542455949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35526164590542124361637299 53289246885813186542455949)
                  ·
                    refine ⟨19983467582179944953420981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53289246885813186542455949 19983467582179944953420981)
                    ·
                      refine ⟨1873450085829369839383217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19983467582179944953420981 1873450085829369839383217)
                      ·
                        rfl

theorem cell23_3648531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_3648531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648531 prefixEnd_3648531 := by exact prefixLift 3648531
  have htrace : WordTrace (prefixWord ++ tailWord_3648531) baseStart_3648531 baseEnd_3648531 := by
    simpa [prefixWord, tailWord_3648531, baseEnd_3648531] using wordTrace_append hprefix tailTrace_3648531
  have hstable : (prefixWord ++ tailWord_3648531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648531).length < 2 ^ (prefixWord ++ tailWord_3648531).sum := by decide
  have hdescent : baseEnd_3648531 < baseStart_3648531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648568 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 7]
def baseStart_3648568 : Nat := 118140960795 + 3648568 * 2 ^ 59
def prefixEnd_3648568 : Nat := 4983230072969 + 3 ^ 40 * 3648568 * 2
def baseEnd_3648568 : Nat := 208163231623731799402283

theorem tailTrace_3648568 : CollatzResearch.WordTrace tailWord_3648568 prefixEnd_3648568 208163231623731799402283 := by
  unfold tailWord_3648568
  simp only [CollatzResearch.WordTrace]
  refine ⟨66537103722934368324965179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88716138297245824433286905 66537103722934368324965179)
  ·
    refine ⟨99805655584401552487447769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66537103722934368324965179 99805655584401552487447769)
    ·
      refine ⟨74854241688301164365585827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99805655584401552487447769 74854241688301164365585827)
      ·
        refine ⟨112281362532451746548378741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74854241688301164365585827 112281362532451746548378741)
        ·
          refine ⟨10526377737417351238910507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112281362532451746548378741 10526377737417351238910507)
          ·
            refine ⟨15789566606126026858365761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10526377737417351238910507 15789566606126026858365761)
            ·
              refine ⟨11842174954594520143774321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15789566606126026858365761 11842174954594520143774321)
              ·
                refine ⟨8881631215945890107830741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11842174954594520143774321 8881631215945890107830741)
                ·
                  refine ⟨208163231623731799402283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8881631215945890107830741 208163231623731799402283)
                  ·
                    rfl

theorem cell23_3648568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 7].length) (baseStart_3648568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648568 prefixEnd_3648568 := by exact prefixLift 3648568
  have htrace : WordTrace (prefixWord ++ tailWord_3648568) baseStart_3648568 baseEnd_3648568 := by
    simpa [prefixWord, tailWord_3648568, baseEnd_3648568] using wordTrace_append hprefix tailTrace_3648568
  have hstable : (prefixWord ++ tailWord_3648568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648568).length < 2 ^ (prefixWord ++ tailWord_3648568).sum := by decide
  have hdescent : baseEnd_3648568 < baseStart_3648568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648582 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3648582 : Nat := 118140960795 + 3648582 * 2 ^ 59
def prefixEnd_3648582 : Nat := 4983230072969 + 3 ^ 40 * 3648582 * 2
def baseEnd_3648582 : Nat := 1873476273342749139845483

theorem tailTrace_3648582 : CollatzResearch.WordTrace tailWord_3648582 prefixEnd_3648582 1873476273342749139845483 := by
  unfold tailWord_3648582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4158584939619313032529375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88716478711878678027293333 4158584939619313032529375)
  ·
    refine ⟨6237877409428969548794063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4158584939619313032529375 6237877409428969548794063)
    ·
      refine ⟨9356816114143454323191095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6237877409428969548794063 9356816114143454323191095)
      ·
        refine ⟨14035224171215181484786643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9356816114143454323191095 14035224171215181484786643)
        ·
          refine ⟨21052836256822772227179965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14035224171215181484786643 21052836256822772227179965)
          ·
            refine ⟨7894813596308539585192487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21052836256822772227179965 7894813596308539585192487)
            ·
              refine ⟨11842220394462809377788731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7894813596308539585192487 11842220394462809377788731)
              ·
                refine ⟨17763330591694214066683097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11842220394462809377788731 17763330591694214066683097)
                ·
                  refine ⟨13322497943770660550012323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17763330591694214066683097 13322497943770660550012323)
                  ·
                    refine ⟨19983746915655990825018485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13322497943770660550012323 19983746915655990825018485)
                    ·
                      refine ⟨1873476273342749139845483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19983746915655990825018485 1873476273342749139845483)
                      ·
                        rfl

theorem cell23_3648582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3648582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648582 prefixEnd_3648582 := by exact prefixLift 3648582
  have htrace : WordTrace (prefixWord ++ tailWord_3648582) baseStart_3648582 baseEnd_3648582 := by
    simpa [prefixWord, tailWord_3648582, baseEnd_3648582] using wordTrace_append hprefix tailTrace_3648582
  have hstable : (prefixWord ++ tailWord_3648582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648582).length < 2 ^ (prefixWord ++ tailWord_3648582).sum := by decide
  have hdescent : baseEnd_3648582 < baseStart_3648582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648608 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 5]
def baseStart_3648608 : Nat := 118140960795 + 3648608 * 2 ^ 59
def prefixEnd_3648608 : Nat := 4983230072969 + 3 ^ 40 * 3648608 * 2
def baseEnd_3648608 : Nat := 1873489623839766038120363

theorem tailTrace_3648608 : CollatzResearch.WordTrace tailWord_3648608 prefixEnd_3648608 1873489623839766038120363 := by
  unfold tailWord_3648608
  simp only [CollatzResearch.WordTrace]
  refine ⟨66537833182861911740693239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88717110910482548987590985 66537833182861911740693239)
  ·
    refine ⟨99806749774292867611039859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66537833182861911740693239 99806749774292867611039859)
    ·
      refine ⟨149710124661439301416559789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99806749774292867611039859 149710124661439301416559789)
      ·
        refine ⟨56141296748039738031209921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149710124661439301416559789 56141296748039738031209921)
        ·
          refine ⟨42105972561029803523407441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56141296748039738031209921 42105972561029803523407441)
          ·
            refine ⟨31579479420772352642555581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42105972561029803523407441 31579479420772352642555581)
            ·
              refine ⟨11842304782789632240958343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31579479420772352642555581 11842304782789632240958343)
              ·
                refine ⟨17763457174184448361437515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11842304782789632240958343 17763457174184448361437515)
                ·
                  refine ⟨26645185761276672542156273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17763457174184448361437515 26645185761276672542156273)
                  ·
                    refine ⟨19983889320957504406617205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26645185761276672542156273 19983889320957504406617205)
                    ·
                      refine ⟨1873489623839766038120363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19983889320957504406617205 1873489623839766038120363)
                      ·
                        rfl

theorem cell23_3648608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_3648608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648608 prefixEnd_3648608 := by exact prefixLift 3648608
  have htrace : WordTrace (prefixWord ++ tailWord_3648608) baseStart_3648608 baseEnd_3648608 := by
    simpa [prefixWord, tailWord_3648608, baseEnd_3648608] using wordTrace_append hprefix tailTrace_3648608
  have hstable : (prefixWord ++ tailWord_3648608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648608).length < 2 ^ (prefixWord ++ tailWord_3648608).sum := by decide
  have hdescent : baseEnd_3648608 < baseStart_3648608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648689 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3648689 : Nat := 118140960795 + 3648689 * 2 ^ 59
def prefixEnd_3648689 : Nat := 4983230072969 + 3 ^ 40 * 3648689 * 2
def baseEnd_3648689 : Nat := 1873531215772780221207491

theorem tailTrace_3648689 : CollatzResearch.WordTrace tailWord_3648689 prefixEnd_3648689 1873531215772780221207491 := by
  unfold tailWord_3648689
  simp only [CollatzResearch.WordTrace]
  refine ⟨133078620678430374315085121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88719080452286916210056747 133078620678430374315085121)
  ·
    refine ⟨99808965508822780736313841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133078620678430374315085121 99808965508822780736313841)
    ·
      refine ⟨74856724131617085552235381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99808965508822780736313841 74856724131617085552235381)
      ·
        refine ⟨7017817887339101770522067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74856724131617085552235381 7017817887339101770522067)
        ·
          refine ⟨10526726831008652655783101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7017817887339101770522067 10526726831008652655783101)
          ·
            refine ⟨3947522561628244745918663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10526726831008652655783101 3947522561628244745918663)
            ·
              refine ⟨5921283842442367118877995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3947522561628244745918663 5921283842442367118877995)
              ·
                refine ⟨8881925763663550678316993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5921283842442367118877995 8881925763663550678316993)
                ·
                  refine ⟨6661444322747663008737745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8881925763663550678316993 6661444322747663008737745)
                  ·
                    refine ⟨4996083242060747256553309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6661444322747663008737745 4996083242060747256553309)
                    ·
                      refine ⟨1873531215772780221207491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4996083242060747256553309 1873531215772780221207491)
                      ·
                        rfl

theorem cell23_3648689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3648689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648689 prefixEnd_3648689 := by exact prefixLift 3648689
  have htrace : WordTrace (prefixWord ++ tailWord_3648689) baseStart_3648689 baseEnd_3648689 := by
    simpa [prefixWord, tailWord_3648689, baseEnd_3648689] using wordTrace_append hprefix tailTrace_3648689
  have hstable : (prefixWord ++ tailWord_3648689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648689).length < 2 ^ (prefixWord ++ tailWord_3648689).sum := by decide
  have hdescent : baseEnd_3648689 < baseStart_3648689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648698 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_3648698 : Nat := 118140960795 + 3648698 * 2 ^ 59
def prefixEnd_3648698 : Nat := 4983230072969 + 3 ^ 40 * 3648698 * 2
def baseEnd_3648698 : Nat := 1873535837098670685994949

theorem tailTrace_3648698 : CollatzResearch.WordTrace tailWord_3648698 prefixEnd_3648698 1873535837098670685994949 := by
  unfold tailWord_3648698
  simp only [CollatzResearch.WordTrace]
  refine ⟨33269737233849442213040687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88719299290265179234775165 33269737233849442213040687)
  ·
    refine ⟨49904605850774163319561031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33269737233849442213040687 49904605850774163319561031)
    ·
      refine ⟨74856908776161244979341547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49904605850774163319561031 74856908776161244979341547)
      ·
        refine ⟨112285363164241867469012321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74856908776161244979341547 112285363164241867469012321)
        ·
          refine ⟨84214022373181400601759241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112285363164241867469012321 84214022373181400601759241)
          ·
            refine ⟨63160516779886050451319431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84214022373181400601759241 63160516779886050451319431)
            ·
              refine ⟨94740775169829075676979147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63160516779886050451319431 94740775169829075676979147)
              ·
                refine ⟨142111162754743613515468721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94740775169829075676979147 142111162754743613515468721)
                ·
                  refine ⟨106583372066057710136601541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142111162754743613515468721 106583372066057710136601541)
                  ·
                    refine ⟨19984382262385820650612789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106583372066057710136601541 19984382262385820650612789)
                    ·
                      refine ⟨1873535837098670685994949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19984382262385820650612789 1873535837098670685994949)
                      ·
                        rfl

theorem cell23_3648698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_3648698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648698 prefixEnd_3648698 := by exact prefixLift 3648698
  have htrace : WordTrace (prefixWord ++ tailWord_3648698) baseStart_3648698 baseEnd_3648698 := by
    simpa [prefixWord, tailWord_3648698, baseEnd_3648698] using wordTrace_append hprefix tailTrace_3648698
  have hstable : (prefixWord ++ tailWord_3648698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648698).length < 2 ^ (prefixWord ++ tailWord_3648698).sum := by decide
  have hdescent : baseEnd_3648698 < baseStart_3648698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648712 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 2, 3, 2]
def baseStart_3648712 : Nat := 118140960795 + 3648712 * 2 ^ 59
def prefixEnd_3648712 : Nat := 4983230072969 + 3 ^ 40 * 3648712 * 2
def baseEnd_3648712 : Nat := 1873543025827833631219885

theorem tailTrace_3648712 : CollatzResearch.WordTrace tailWord_3648712 prefixEnd_3648712 1873543025827833631219885 := by
  unfold tailWord_3648712
  simp only [CollatzResearch.WordTrace]
  refine ⟨66539729778673524621586195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88719639704898032828781593 66539729778673524621586195)
  ·
    refine ⟨99809594668010286932379293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66539729778673524621586195 99809594668010286932379293)
    ·
      refine ⟨37428598000503857599642235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99809594668010286932379293 37428598000503857599642235)
      ·
        refine ⟨56142897000755786399463353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37428598000503857599642235 56142897000755786399463353)
        ·
          refine ⟨42107172750566839799597515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56142897000755786399463353 42107172750566839799597515)
          ·
            refine ⟨63160759125850259699396273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42107172750566839799597515 63160759125850259699396273)
            ·
              refine ⟨47370569344387694774547205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63160759125850259699396273 47370569344387694774547205)
              ·
                refine ⟨8881981752072692770227601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47370569344387694774547205 8881981752072692770227601)
                ·
                  refine ⟨6661486314054519577670701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8881981752072692770227601 6661486314054519577670701)
                  ·
                    refine ⟨2498057367770444841626513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6661486314054519577670701 2498057367770444841626513)
                    ·
                      refine ⟨1873543025827833631219885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498057367770444841626513 1873543025827833631219885)
                      ·
                        rfl

theorem cell23_3648712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_3648712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648712 prefixEnd_3648712 := by exact prefixLift 3648712
  have htrace : WordTrace (prefixWord ++ tailWord_3648712) baseStart_3648712 baseEnd_3648712 := by
    simpa [prefixWord, tailWord_3648712, baseEnd_3648712] using wordTrace_append hprefix tailTrace_3648712
  have hstable : (prefixWord ++ tailWord_3648712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648712).length < 2 ^ (prefixWord ++ tailWord_3648712).sum := by decide
  have hdescent : baseEnd_3648712 < baseStart_3648712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648726 : List Nat := [5, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_3648726 : Nat := 118140960795 + 3648726 * 2 ^ 59
def prefixEnd_3648726 : Nat := 4983230072969 + 3 ^ 40 * 3648726 * 2
def baseEnd_3648726 : Nat := 208172246061888508493869

theorem tailTrace_3648726 : CollatzResearch.WordTrace tailWord_3648726 prefixEnd_3648726 208172246061888508493869 := by
  unfold tailWord_3648726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8317498136206020602136377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88719980119530886422788021 8317498136206020602136377)
  ·
    refine ⟨6238123602154515451602283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8317498136206020602136377 6238123602154515451602283)
    ·
      refine ⟨9357185403231773177403425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6238123602154515451602283 9357185403231773177403425)
      ·
        refine ⟨7017889052423829883052569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9357185403231773177403425 7017889052423829883052569)
        ·
          refine ⟨5263416789317872412289427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7017889052423829883052569 5263416789317872412289427)
          ·
            refine ⟨7895125183976808618434141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5263416789317872412289427 7895125183976808618434141)
            ·
              refine ⟨2960671943991303231912803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7895125183976808618434141 2960671943991303231912803)
              ·
                refine ⟨4441007915986954847869205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2960671943991303231912803 4441007915986954847869205)
                ·
                  refine ⟨208172246061888508493869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4441007915986954847869205 208172246061888508493869)
                  ·
                    rfl

theorem cell23_3648726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_3648726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648726 prefixEnd_3648726 := by exact prefixLift 3648726
  have htrace : WordTrace (prefixWord ++ tailWord_3648726) baseStart_3648726 baseEnd_3648726 := by
    simpa [prefixWord, tailWord_3648726, baseEnd_3648726] using wordTrace_append hprefix tailTrace_3648726
  have hstable : (prefixWord ++ tailWord_3648726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648726).length < 2 ^ (prefixWord ++ tailWord_3648726).sum := by decide
  have hdescent : baseEnd_3648726 < baseStart_3648726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648735 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 1, 6]
def baseStart_3648735 : Nat := 118140960795 + 3648735 * 2 ^ 59
def prefixEnd_3648735 : Nat := 4983230072969 + 3 ^ 40 * 3648735 * 2
def baseEnd_3648735 : Nat := 624518278627629013744093

theorem tailTrace_3648735 : CollatzResearch.WordTrace tailWord_3648735 prefixEnd_3648735 624518278627629013744093 := by
  unfold tailWord_3648735
  simp only [CollatzResearch.WordTrace]
  refine ⟨133080298436263724171259659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88720198957509149447506439 133080298436263724171259659)
  ·
    refine ⟨199620447654395586256889489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133080298436263724171259659 199620447654395586256889489)
    ·
      refine ⟨149715335740796689692667117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199620447654395586256889489 149715335740796689692667117)
      ·
        refine ⟨56143250902798758634750169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149715335740796689692667117 56143250902798758634750169)
        ·
          refine ⟨42107438177099068976062627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56143250902798758634750169 42107438177099068976062627)
          ·
            refine ⟨63161157265648603464093941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42107438177099068976062627 63161157265648603464093941)
            ·
              refine ⟨5921358493654556574758807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63161157265648603464093941 5921358493654556574758807)
              ·
                refine ⟨8882037740481834862138211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5921358493654556574758807 8882037740481834862138211)
                ·
                  refine ⟨13323056610722752293207317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8882037740481834862138211 13323056610722752293207317)
                  ·
                    refine ⟨624518278627629013744093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13323056610722752293207317 624518278627629013744093)
                    ·
                      rfl

theorem cell23_3648735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 6].length) (baseStart_3648735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648735 prefixEnd_3648735 := by exact prefixLift 3648735
  have htrace : WordTrace (prefixWord ++ tailWord_3648735) baseStart_3648735 baseEnd_3648735 := by
    simpa [prefixWord, tailWord_3648735, baseEnd_3648735] using wordTrace_append hprefix tailTrace_3648735
  have hstable : (prefixWord ++ tailWord_3648735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648735).length < 2 ^ (prefixWord ++ tailWord_3648735).sum := by decide
  have hdescent : baseEnd_3648735 < baseStart_3648735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648762 : List Nat := [3, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3]
def baseStart_3648762 : Nat := 118140960795 + 3648762 * 2 ^ 59
def prefixEnd_3648762 : Nat := 4983230072969 + 3 ^ 40 * 3648762 * 2
def baseEnd_3648762 : Nat := 1873568699860558435594655

theorem tailTrace_3648762 : CollatzResearch.WordTrace tailWord_3648762 prefixEnd_3648762 1873568699860558435594655 := by
  unfold tailWord_3648762
  simp only [CollatzResearch.WordTrace]
  refine ⟨33270320801791476945623135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88720855471443938521661693 33270320801791476945623135)
  ·
    refine ⟨49905481202687215418434703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33270320801791476945623135 49905481202687215418434703)
    ·
      refine ⟨74858221804030823127652055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49905481202687215418434703 74858221804030823127652055)
      ·
        refine ⟨112287332706046234691478083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74858221804030823127652055 112287332706046234691478083)
        ·
          refine ⟨168430999059069352037217125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112287332706046234691478083 168430999059069352037217125)
          ·
            refine ⟨31580812323575503506978211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168430999059069352037217125 31580812323575503506978211)
            ·
              refine ⟨47371218485363255260467317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31580812323575503506978211 47371218485363255260467317)
              ·
                refine ⟨4441051733002805180668811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47371218485363255260467317 4441051733002805180668811)
                ·
                  refine ⟨6661577599504207771003217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4441051733002805180668811 6661577599504207771003217)
                  ·
                    refine ⟨4996183199628155828252413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6661577599504207771003217 4996183199628155828252413)
                    ·
                      refine ⟨1873568699860558435594655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4996183199628155828252413 1873568699860558435594655)
                      ·
                        rfl

theorem cell23_3648762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_3648762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648762 prefixEnd_3648762 := by exact prefixLift 3648762
  have htrace : WordTrace (prefixWord ++ tailWord_3648762) baseStart_3648762 baseEnd_3648762 := by
    simpa [prefixWord, tailWord_3648762, baseEnd_3648762] using wordTrace_append hprefix tailTrace_3648762
  have hstable : (prefixWord ++ tailWord_3648762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648762).length < 2 ^ (prefixWord ++ tailWord_3648762).sum := by decide
  have hdescent : baseEnd_3648762 < baseStart_3648762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648770 : List Nat := [3, 4, 1, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_3648770 : Nat := 118140960795 + 3648770 * 2 ^ 59
def prefixEnd_3648770 : Nat := 4983230072969 + 3 ^ 40 * 3648770 * 2
def baseEnd_3648770 : Nat := 1873572807705794404294619

theorem tailTrace_3648770 : CollatzResearch.WordTrace tailWord_3648770 prefixEnd_3648770 1873572807705794404294619 := by
  unfold tailWord_3648770
  simp only [CollatzResearch.WordTrace]
  refine ⟨33270393747784231287195941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88721049994091283432522509 33270393747784231287195941)
  ·
    refine ⟨6238198827709543366349239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33270393747784231287195941 6238198827709543366349239)
    ·
      refine ⟨9357298241564315049523859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6238198827709543366349239 9357298241564315049523859)
      ·
        refine ⟨14035947362346472574285789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9357298241564315049523859 14035947362346472574285789)
        ·
          refine ⟨5263480260879927215357171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14035947362346472574285789 5263480260879927215357171)
          ·
            refine ⟨7895220391319890823035757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5263480260879927215357171 7895220391319890823035757)
            ·
              refine ⟨2960707646744959058638409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7895220391319890823035757 2960707646744959058638409)
              ·
                refine ⟨2220530735058719293978807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2960707646744959058638409 2220530735058719293978807)
                ·
                  refine ⟨3330796102588078940968211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2220530735058719293978807 3330796102588078940968211)
                  ·
                    refine ⟨4996194153882118411452317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3330796102588078940968211 4996194153882118411452317)
                    ·
                      refine ⟨1873572807705794404294619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4996194153882118411452317 1873572807705794404294619)
                      ·
                        rfl

theorem cell23_3648770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_3648770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648770 prefixEnd_3648770 := by exact prefixLift 3648770
  have htrace : WordTrace (prefixWord ++ tailWord_3648770) baseStart_3648770 baseEnd_3648770 := by
    simpa [prefixWord, tailWord_3648770, baseEnd_3648770] using wordTrace_append hprefix tailTrace_3648770
  have hstable : (prefixWord ++ tailWord_3648770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648770).length < 2 ^ (prefixWord ++ tailWord_3648770).sum := by decide
  have hdescent : baseEnd_3648770 < baseStart_3648770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648813 : List Nat := [1, 5, 3, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_3648813 : Nat := 118140960795 + 3648813 * 2 ^ 59
def prefixEnd_3648813 : Nat := 4983230072969 + 3 ^ 40 * 3648813 * 2
def baseEnd_3648813 : Nat := 1873594887373937736056921

theorem tailTrace_3648813 : CollatzResearch.WordTrace tailWord_3648813 prefixEnd_3648813 1873594887373937736056921 := by
  unfold tailWord_3648813
  simp only [CollatzResearch.WordTrace]
  refine ⟨133083143329981143492599093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88722095553320762328399395 133083143329981143492599093)
  ·
    refine ⟨12476544687185732202431165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133083143329981143492599093 12476544687185732202431165)
    ·
      refine ⟨4678704257694649575911687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12476544687185732202431165 4678704257694649575911687)
      ·
        refine ⟨7018056386541974363867531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4678704257694649575911687 7018056386541974363867531)
        ·
          refine ⟨10527084579812961545801297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7018056386541974363867531 10527084579812961545801297)
          ·
            refine ⟨7895313434859721159350973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10527084579812961545801297 7895313434859721159350973)
            ·
              refine ⟨2960742538072395434756615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7895313434859721159350973 2960742538072395434756615)
              ·
                refine ⟨4441113807108593152134923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2960742538072395434756615 4441113807108593152134923)
                ·
                  refine ⟨6661670710662889728202385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4441113807108593152134923 6661670710662889728202385)
                  ·
                    refine ⟨4996253032997167296151789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6661670710662889728202385 4996253032997167296151789)
                    ·
                      refine ⟨1873594887373937736056921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4996253032997167296151789 1873594887373937736056921)
                      ·
                        rfl

theorem cell23_3648813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_3648813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648813 prefixEnd_3648813 := by exact prefixLift 3648813
  have htrace : WordTrace (prefixWord ++ tailWord_3648813) baseStart_3648813 baseEnd_3648813 := by
    simpa [prefixWord, tailWord_3648813, baseEnd_3648813] using wordTrace_append hprefix tailTrace_3648813
  have hstable : (prefixWord ++ tailWord_3648813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648813).length < 2 ^ (prefixWord ++ tailWord_3648813).sum := by decide
  have hdescent : baseEnd_3648813 < baseStart_3648813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648832 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 3, 4, 2]
def baseStart_3648832 : Nat := 118140960795 + 3648832 * 2 ^ 59
def prefixEnd_3648832 : Nat := 4983230072969 + 3 ^ 40 * 3648832 * 2
def baseEnd_3648832 : Nat := 1873604643506373161719333

theorem tailTrace_3648832 : CollatzResearch.WordTrace tailWord_3648832 prefixEnd_3648832 1873604643506373161719333 := by
  unfold tailWord_3648832
  simp only [CollatzResearch.WordTrace]
  refine ⟨66541918158456154868770375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88722557544608206491693833 66541918158456154868770375)
  ·
    refine ⟨99812877237684232303155563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66541918158456154868770375 99812877237684232303155563)
    ·
      refine ⟨149719315856526348454733345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99812877237684232303155563 149719315856526348454733345)
      ·
        refine ⟨112289486892394761341050009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149719315856526348454733345 112289486892394761341050009)
        ·
          refine ⟨84217115169296071005787507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112289486892394761341050009 84217115169296071005787507)
          ·
            refine ⟨126325672753944106508681261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84217115169296071005787507 126325672753944106508681261)
            ·
              refine ⟨47372127282729039940755473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126325672753944106508681261 47372127282729039940755473)
              ·
                refine ⟨35529095462046779955566605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47372127282729039940755473 35529095462046779955566605)
                ·
                  refine ⟨13323410798267542483337477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35529095462046779955566605 13323410798267542483337477)
                  ·
                    refine ⟨2498139524675164215625777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13323410798267542483337477 2498139524675164215625777)
                    ·
                      refine ⟨1873604643506373161719333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498139524675164215625777 1873604643506373161719333)
                      ·
                        rfl

theorem cell23_3648832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 4, 2].length) (baseStart_3648832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648832 prefixEnd_3648832 := by exact prefixLift 3648832
  have htrace : WordTrace (prefixWord ++ tailWord_3648832) baseStart_3648832 baseEnd_3648832 := by
    simpa [prefixWord, tailWord_3648832, baseEnd_3648832] using wordTrace_append hprefix tailTrace_3648832
  have hstable : (prefixWord ++ tailWord_3648832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648832).length < 2 ^ (prefixWord ++ tailWord_3648832).sum := by decide
  have hdescent : baseEnd_3648832 < baseStart_3648832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648836 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_3648836 : Nat := 118140960795 + 3648836 * 2 ^ 59
def prefixEnd_3648836 : Nat := 4983230072969 + 3 ^ 40 * 3648836 * 2
def baseEnd_3648836 : Nat := 1873606697428991146069315

theorem tailTrace_3648836 : CollatzResearch.WordTrace tailWord_3648836 prefixEnd_3648836 1873606697428991146069315 := by
  unfold tailWord_3648836
  simp only [CollatzResearch.WordTrace]
  refine ⟨66541991104448909210343181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88722654805931878947124241 66541991104448909210343181)
  ·
    refine ⟨24953246664168340953878693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66541991104448909210343181 24953246664168340953878693)
    ·
      refine ⟨4678733749531563928852255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24953246664168340953878693 4678733749531563928852255)
      ·
        refine ⟨7018100624297345893278383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4678733749531563928852255 7018100624297345893278383)
        ·
          refine ⟨10527150936446018839917575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7018100624297345893278383 10527150936446018839917575)
          ·
            refine ⟨15790726404669028259876363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10527150936446018839917575 15790726404669028259876363)
            ·
              refine ⟨23686089607003542389814545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15790726404669028259876363 23686089607003542389814545)
              ·
                refine ⟨17764567205252656792360909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23686089607003542389814545 17764567205252656792360909)
                ·
                  refine ⟨6661712701969746297135341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17764567205252656792360909 6661712701969746297135341)
                  ·
                    refine ⟨2498142263238654861425753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6661712701969746297135341 2498142263238654861425753)
                    ·
                      refine ⟨1873606697428991146069315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498142263238654861425753 1873606697428991146069315)
                      ·
                        rfl

theorem cell23_3648836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_3648836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648836 prefixEnd_3648836 := by exact prefixLift 3648836
  have htrace : WordTrace (prefixWord ++ tailWord_3648836) baseStart_3648836 baseEnd_3648836 := by
    simpa [prefixWord, tailWord_3648836, baseEnd_3648836] using wordTrace_append hprefix tailTrace_3648836
  have hstable : (prefixWord ++ tailWord_3648836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648836).length < 2 ^ (prefixWord ++ tailWord_3648836).sum := by decide
  have hdescent : baseEnd_3648836 < baseStart_3648836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648849 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 1, 4, 2]
def baseStart_3648849 : Nat := 118140960795 + 3648849 * 2 ^ 59
def prefixEnd_3648849 : Nat := 4983230072969 + 3 ^ 40 * 3648849 * 2
def baseEnd_3648849 : Nat := 1873613372677499595206755

theorem tailTrace_3648849 : CollatzResearch.WordTrace tailWord_3648849 prefixEnd_3648849 1873613372677499595206755 := by
  unfold tailWord_3648849
  simp only [CollatzResearch.WordTrace]
  refine ⟨133084456357850721640909601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88722970905233814427273067 133084456357850721640909601)
  ·
    refine ⟨99813342268388041230682201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133084456357850721640909601 99813342268388041230682201)
    ·
      refine ⟨74860006701291030923011651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99813342268388041230682201 74860006701291030923011651)
      ·
        refine ⟨112290010051936546384517477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74860006701291030923011651 112290010051936546384517477)
        ·
          refine ⟨21054376884738102447097027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112290010051936546384517477 21054376884738102447097027)
          ·
            refine ⟨31581565327107153670645541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21054376884738102447097027 31581565327107153670645541)
            ·
              refine ⟨5921543498832591313246039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31581565327107153670645541 5921543498832591313246039)
              ·
                refine ⟨8882315248248886969869059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5921543498832591313246039 8882315248248886969869059)
                ·
                  refine ⟨13323472872373330454803589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8882315248248886969869059 13323472872373330454803589)
                  ·
                    refine ⟨2498151163569999460275673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13323472872373330454803589 2498151163569999460275673)
                    ·
                      refine ⟨1873613372677499595206755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498151163569999460275673 1873613372677499595206755)
                      ·
                        rfl

theorem cell23_3648849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 4, 2].length) (baseStart_3648849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648849 prefixEnd_3648849 := by exact prefixLift 3648849
  have htrace : WordTrace (prefixWord ++ tailWord_3648849) baseStart_3648849 baseEnd_3648849 := by
    simpa [prefixWord, tailWord_3648849, baseEnd_3648849] using wordTrace_append hprefix tailTrace_3648849
  have hstable : (prefixWord ++ tailWord_3648849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648849).length < 2 ^ (prefixWord ++ tailWord_3648849).sum := by decide
  have hdescent : baseEnd_3648849 < baseStart_3648849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
