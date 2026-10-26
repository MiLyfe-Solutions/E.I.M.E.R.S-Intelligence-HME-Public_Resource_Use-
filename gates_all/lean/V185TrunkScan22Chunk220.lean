import V185TrunkScan22Chunk219

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1960500 : List Nat := [2, 5, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_1960500 : Nat := 118140960795 + 1960500 * 2 ^ 59
def prefixEnd_1960500 : Nat := 4983230072969 + 3 ^ 40 * 1960500 * 2
def baseEnd_1960500 : Nat := 671119215426456512289221

theorem tailTrace_1960500 : CollatzResearch.WordTrace tailWord_1960500 prefixEnd_1960500 671119215426456512289221 := by
  unfold tailWord_1960500
  simp only [CollatzResearch.WordTrace]
  refine ⟨35752654698725400794095477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47670206264967201058793969 35752654698725400794095477)
  ·
    refine ⟨3351811378005506324446451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35752654698725400794095477 3351811378005506324446451)
    ·
      refine ⟨5027717067008259486669677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3351811378005506324446451 5027717067008259486669677)
      ·
        refine ⟨1885393900128097307501129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5027717067008259486669677 1885393900128097307501129)
        ·
          refine ⟨1414045425096072980625847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1885393900128097307501129 1414045425096072980625847)
          ·
            refine ⟨2121068137644109470938771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414045425096072980625847 2121068137644109470938771)
            ·
              refine ⟨3181602206466164206408157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121068137644109470938771 3181602206466164206408157)
              ·
                refine ⟨1193100827424811577403059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3181602206466164206408157 1193100827424811577403059)
                ·
                  refine ⟨1789651241137217366104589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193100827424811577403059 1789651241137217366104589)
                  ·
                    refine ⟨671119215426456512289221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1789651241137217366104589 671119215426456512289221)
                    ·
                      rfl

theorem cell22_1960500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_1960500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960500 prefixEnd_1960500 := by exact prefixLift 1960500
  have htrace : WordTrace (prefixWord ++ tailWord_1960500) baseStart_1960500 baseEnd_1960500 := by
    simpa [prefixWord, tailWord_1960500, baseEnd_1960500] using wordTrace_append hprefix tailTrace_1960500
  have hstable : (prefixWord ++ tailWord_1960500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960500).length < 2 ^ (prefixWord ++ tailWord_1960500).sum := by decide
  have hdescent : baseEnd_1960500 < baseStart_1960500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960503 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 1, 6]
def baseStart_1960503 : Nat := 118140960795 + 1960503 * 2 ^ 59
def prefixEnd_1960503 : Nat := 4983230072969 + 3 ^ 40 * 1960503 * 2
def baseEnd_1960503 : Nat := 671120242387765504464211

theorem tailTrace_1960503 : CollatzResearch.WordTrace tailWord_1960503 prefixEnd_1960503 671120242387765504464211 := by
  unfold tailWord_1960503
  simp only [CollatzResearch.WordTrace]
  refine ⟨71505418816439933100550163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47670279210959955400366775 71505418816439933100550163)
  ·
    refine ⟨107258128224659899650825245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71505418816439933100550163 107258128224659899650825245)
    ·
      refine ⟨40221798084247462369059467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107258128224659899650825245 40221798084247462369059467)
      ·
        refine ⟨60332697126371193553589201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40221798084247462369059467 60332697126371193553589201)
        ·
          refine ⟨45249522844778395165191901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60332697126371193553589201 45249522844778395165191901)
          ·
            refine ⟨16968571066791898186946963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45249522844778395165191901 16968571066791898186946963)
            ·
              refine ⟨25452856600187847280420445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16968571066791898186946963 25452856600187847280420445)
              ·
                refine ⟨9544821225070442730157667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25452856600187847280420445 9544821225070442730157667)
                ·
                  refine ⟨14317231837605664095236501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9544821225070442730157667 14317231837605664095236501)
                  ·
                    refine ⟨671120242387765504464211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14317231837605664095236501 671120242387765504464211)
                    ·
                      rfl

theorem cell22_1960503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_1960503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960503 prefixEnd_1960503 := by exact prefixLift 1960503
  have htrace : WordTrace (prefixWord ++ tailWord_1960503) baseStart_1960503 baseEnd_1960503 := by
    simpa [prefixWord, tailWord_1960503, baseEnd_1960503] using wordTrace_append hprefix tailTrace_1960503
  have hstable : (prefixWord ++ tailWord_1960503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960503).length < 2 ^ (prefixWord ++ tailWord_1960503).sum := by decide
  have hdescent : baseEnd_1960503 < baseStart_1960503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960505 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 6, 3]
def baseStart_1960505 : Nat := 118140960795 + 1960505 * 2 ^ 59
def prefixEnd_1960505 : Nat := 4983230072969 + 3 ^ 40 * 1960505 * 2
def baseEnd_1960505 : Nat := 671120927028638165914205

theorem tailTrace_1960505 : CollatzResearch.WordTrace tailWord_1960505 prefixEnd_1960505 671120927028638165914205 := by
  unfold tailWord_1960505
  simp only [CollatzResearch.WordTrace]
  refine ⟨71505491762432687442122969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47670327841621791628081979 71505491762432687442122969)
  ·
    refine ⟨53629118821824515581592227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71505491762432687442122969 53629118821824515581592227)
    ·
      refine ⟨80443678232736773372388341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53629118821824515581592227 80443678232736773372388341)
      ·
        refine ⟨7541594834319072503661407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80443678232736773372388341 7541594834319072503661407)
        ·
          refine ⟨11312392251478608755492111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7541594834319072503661407 11312392251478608755492111)
          ·
            refine ⟨16968588377217913133238167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11312392251478608755492111 16968588377217913133238167)
            ·
              refine ⟨25452882565826869699857251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16968588377217913133238167 25452882565826869699857251)
              ·
                refine ⟨38179323848740304549785877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25452882565826869699857251 38179323848740304549785877)
                ·
                  refine ⟨1789655805409701775771213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38179323848740304549785877 1789655805409701775771213)
                  ·
                    refine ⟨671120927028638165914205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1789655805409701775771213 671120927028638165914205)
                    ·
                      rfl

theorem cell22_1960505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 3].length) (baseStart_1960505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960505 prefixEnd_1960505 := by exact prefixLift 1960505
  have htrace : WordTrace (prefixWord ++ tailWord_1960505) baseStart_1960505 baseEnd_1960505 := by
    simpa [prefixWord, tailWord_1960505, baseEnd_1960505] using wordTrace_append hprefix tailTrace_1960505
  have hstable : (prefixWord ++ tailWord_1960505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960505).length < 2 ^ (prefixWord ++ tailWord_1960505).sum := by decide
  have hdescent : baseEnd_1960505 < baseStart_1960505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960563 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 7]
def baseStart_1960563 : Nat := 118140960795 + 1960563 * 2 ^ 59
def prefixEnd_1960563 : Nat := 4983230072969 + 3 ^ 40 * 1960563 * 2
def baseEnd_1960563 : Nat := 223713593871315115988009

theorem tailTrace_1960563 : CollatzResearch.WordTrace tailWord_1960563 prefixEnd_1960563 223713593871315115988009 := by
  unfold tailWord_1960563
  simp only [CollatzResearch.WordTrace]
  refine ⟨71507607196222563347734343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47671738130815042231822895 71507607196222563347734343)
  ·
    refine ⟨107261410794333845021601515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71507607196222563347734343 107261410794333845021601515)
    ·
      refine ⟨160892116191500767532402273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107261410794333845021601515 160892116191500767532402273)
      ·
        refine ⟨120669087143625575649301705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160892116191500767532402273 120669087143625575649301705)
        ·
          refine ⟨90501815357719181736976279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120669087143625575649301705 90501815357719181736976279)
          ·
            refine ⟨135752723036578772605464419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90501815357719181736976279 135752723036578772605464419)
            ·
              refine ⟨203629084554868158908196629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135752723036578772605464419 203629084554868158908196629)
              ·
                refine ⟨9545113338509444948821717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 203629084554868158908196629 9545113338509444948821717)
                ·
                  refine ⟨223713593871315115988009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9545113338509444948821717 223713593871315115988009)
                  ·
                    rfl

theorem cell22_1960563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 7].length) (baseStart_1960563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960563 prefixEnd_1960563 := by exact prefixLift 1960563
  have htrace : WordTrace (prefixWord ++ tailWord_1960563) baseStart_1960563 baseEnd_1960563 := by
    simpa [prefixWord, tailWord_1960563, baseEnd_1960563] using wordTrace_append hprefix tailTrace_1960563
  have hstable : (prefixWord ++ tailWord_1960563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960563).length < 2 ^ (prefixWord ++ tailWord_1960563).sum := by decide
  have hdescent : baseEnd_1960563 < baseStart_1960563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960627 : List Nat := [1, 1, 1, 2, 3, 5, 1, 3, 1, 4]
def baseStart_1960627 : Nat := 118140960795 + 1960627 * 2 ^ 59
def prefixEnd_1960627 : Nat := 4983230072969 + 3 ^ 40 * 1960627 * 2
def baseEnd_1960627 : Nat := 671162690121870514363831

theorem tailTrace_1960627 : CollatzResearch.WordTrace tailWord_1960627 prefixEnd_1960627 671162690121870514363831 := by
  unfold tailWord_1960627
  simp only [CollatzResearch.WordTrace]
  refine ⟨71509941467990702278064135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47673294311993801518709423 71509941467990702278064135)
  ·
    refine ⟨107264912201986053417096203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71509941467990702278064135 107264912201986053417096203)
    ·
      refine ⟨160897368302979080125644305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107264912201986053417096203 160897368302979080125644305)
      ·
        refine ⟨120673026227234310094233229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160897368302979080125644305 120673026227234310094233229)
        ·
          refine ⟨45252384835212866285337461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120673026227234310094233229 45252384835212866285337461)
          ·
            refine ⟨4242411078301206214250387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45252384835212866285337461 4242411078301206214250387)
            ·
              refine ⟨6363616617451809321375581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4242411078301206214250387 6363616617451809321375581)
              ·
                refine ⟨2386356231544428495515843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6363616617451809321375581 2386356231544428495515843)
                ·
                  refine ⟨3579534347316642743273765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386356231544428495515843 3579534347316642743273765)
                  ·
                    refine ⟨671162690121870514363831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3579534347316642743273765 671162690121870514363831)
                    ·
                      rfl

theorem cell22_1960627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 4].length) (baseStart_1960627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960627 prefixEnd_1960627 := by exact prefixLift 1960627
  have htrace : WordTrace (prefixWord ++ tailWord_1960627) baseStart_1960627 baseEnd_1960627 := by
    simpa [prefixWord, tailWord_1960627, baseEnd_1960627] using wordTrace_append hprefix tailTrace_1960627
  have hstable : (prefixWord ++ tailWord_1960627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960627).length < 2 ^ (prefixWord ++ tailWord_1960627).sum := by decide
  have hdescent : baseEnd_1960627 < baseStart_1960627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960661 : List Nat := [1, 3, 2, 5, 1, 1, 2, 2, 1, 4]
def baseStart_1960661 : Nat := 118140960795 + 1960661 * 2 ^ 59
def prefixEnd_1960661 : Nat := 4983230072969 + 3 ^ 40 * 1960661 * 2
def baseEnd_1960661 : Nat := 671174329016705759013727

theorem tailTrace_1960661 : CollatzResearch.WordTrace tailWord_1960661 prefixEnd_1960661 671174329016705759013727 := by
  unfold tailWord_1960661
  simp only [CollatzResearch.WordTrace]
  refine ⟨71511181549867526084801837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47674121033245017389867891 71511181549867526084801837)
  ·
    refine ⟨26816693081200322281800689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71511181549867526084801837 26816693081200322281800689)
    ·
      refine ⟨20112519810900241711350517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26816693081200322281800689 20112519810900241711350517)
      ·
        refine ⟨1885548732271897660439111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20112519810900241711350517 1885548732271897660439111)
        ·
          refine ⟨2828323098407846490658667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885548732271897660439111 2828323098407846490658667)
          ·
            refine ⟨4242484647611769735988001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2828323098407846490658667 4242484647611769735988001)
            ·
              refine ⟨3181863485708827301991001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4242484647611769735988001 3181863485708827301991001)
              ·
                refine ⟨2386397614281620476493251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3181863485708827301991001 2386397614281620476493251)
                ·
                  refine ⟨3579596421422430714739877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386397614281620476493251 3579596421422430714739877)
                  ·
                    refine ⟨671174329016705759013727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3579596421422430714739877 671174329016705759013727)
                    ·
                      rfl

theorem cell22_1960661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_1960661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960661 prefixEnd_1960661 := by exact prefixLift 1960661
  have htrace : WordTrace (prefixWord ++ tailWord_1960661) baseStart_1960661 baseEnd_1960661 := by
    simpa [prefixWord, tailWord_1960661, baseEnd_1960661] using wordTrace_append hprefix tailTrace_1960661
  have hstable : (prefixWord ++ tailWord_1960661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960661).length < 2 ^ (prefixWord ++ tailWord_1960661).sum := by decide
  have hdescent : baseEnd_1960661 < baseStart_1960661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960693 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 6]
def baseStart_1960693 : Nat := 118140960795 + 1960693 * 2 ^ 59
def prefixEnd_1960693 : Nat := 4983230072969 + 3 ^ 40 * 1960693 * 2
def baseEnd_1960693 : Nat := 223728427756889447404543

theorem tailTrace_1960693 : CollatzResearch.WordTrace tailWord_1960693 prefixEnd_1960693 223728427756889447404543 := by
  unfold tailWord_1960693
  simp only [CollatzResearch.WordTrace]
  refine ⟨71512348685751595549966733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47674899123834397033311155 71512348685751595549966733)
  ·
    refine ⟨26817130757156848331237525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71512348685751595549966733 26817130757156848331237525)
    ·
      refine ⟨1257053004241727265526759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 26817130757156848331237525 1257053004241727265526759)
      ·
        refine ⟨1885579506362590898290139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1257053004241727265526759 1885579506362590898290139)
        ·
          refine ⟨2828369259543886347435209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885579506362590898290139 2828369259543886347435209)
          ·
            refine ⟨2121276944657914760576407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2828369259543886347435209 2121276944657914760576407)
            ·
              refine ⟨3181915416986872140864611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2121276944657914760576407 3181915416986872140864611)
              ·
                refine ⟨4772873125480308211296917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3181915416986872140864611 4772873125480308211296917)
                ·
                  refine ⟨223728427756889447404543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4772873125480308211296917 223728427756889447404543)
                  ·
                    rfl

theorem cell22_1960693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_1960693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960693 prefixEnd_1960693 := by exact prefixLift 1960693
  have htrace : WordTrace (prefixWord ++ tailWord_1960693) baseStart_1960693 baseEnd_1960693 := by
    simpa [prefixWord, tailWord_1960693, baseEnd_1960693] using wordTrace_append hprefix tailTrace_1960693
  have hstable : (prefixWord ++ tailWord_1960693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960693).length < 2 ^ (prefixWord ++ tailWord_1960693).sum := by decide
  have hdescent : baseEnd_1960693 < baseStart_1960693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960777 : List Nat := [1, 2, 1, 1, 2, 6, 1, 2, 6]
def baseStart_1960777 : Nat := 118140960795 + 1960777 * 2 ^ 59
def prefixEnd_1960777 : Nat := 4983230072969 + 3 ^ 40 * 1960777 * 2
def baseEnd_1960777 : Nat := 223738012729106707704457

theorem tailTrace_1960777 : CollatzResearch.WordTrace tailWord_1960777 prefixEnd_1960777 223738012729106707704457 := by
  unfold tailWord_1960777
  simp only [CollatzResearch.WordTrace]
  refine ⟨71515412417447277896024585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47676941611631518597349723 71515412417447277896024585)
  ·
    refine ⟨53636559313085458422018439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71515412417447277896024585 53636559313085458422018439)
    ·
      refine ⟨80454838969628187633027659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53636559313085458422018439 80454838969628187633027659)
      ·
        refine ⟨120682258454442281449541489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80454838969628187633027659 120682258454442281449541489)
        ·
          refine ⟨90511693840831711087156117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120682258454442281449541489 90511693840831711087156117)
          ·
            refine ⟨4242735648788986457210443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90511693840831711087156117 4242735648788986457210443)
            ·
              refine ⟨6364103473183479685815665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4242735648788986457210443 6364103473183479685815665)
              ·
                refine ⟨4773077604887609764361749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6364103473183479685815665 4773077604887609764361749)
                ·
                  refine ⟨223738012729106707704457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4773077604887609764361749 223738012729106707704457)
                  ·
                    rfl

theorem cell22_1960777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_1960777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960777 prefixEnd_1960777 := by exact prefixLift 1960777
  have htrace : WordTrace (prefixWord ++ tailWord_1960777) baseStart_1960777 baseEnd_1960777 := by
    simpa [prefixWord, tailWord_1960777, baseEnd_1960777] using wordTrace_append hprefix tailTrace_1960777
  have hstable : (prefixWord ++ tailWord_1960777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960777).length < 2 ^ (prefixWord ++ tailWord_1960777).sum := by decide
  have hdescent : baseEnd_1960777 < baseStart_1960777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960794 : List Nat := [3, 1, 1, 2, 1, 4, 1, 5, 4]
def baseStart_1960794 : Nat := 118140960795 + 1960794 * 2 ^ 59
def prefixEnd_1960794 : Nat := 4983230072969 + 3 ^ 40 * 1960794 * 2
def baseEnd_1960794 : Nat := 223739952544912581812773

theorem tailTrace_1960794 : CollatzResearch.WordTrace tailWord_1960794 prefixEnd_1960794 223739952544912581812773 := by
  unfold tailWord_1960794
  simp only [CollatzResearch.WordTrace]
  refine ⟨17879008114596422449848359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47677354972257126532928957 17879008114596422449848359)
  ·
    refine ⟨26818512171894633674772539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17879008114596422449848359 26818512171894633674772539)
    ·
      refine ⟨40227768257841950512158809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26818512171894633674772539 40227768257841950512158809)
      ·
        refine ⟨30170826193381462884119107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40227768257841950512158809 30170826193381462884119107)
        ·
          refine ⟨45256239290072194326178661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30170826193381462884119107 45256239290072194326178661)
          ·
            refine ⟨8485544866888536436158499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45256239290072194326178661 8485544866888536436158499)
            ·
              refine ⟨12728317300332804654237749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8485544866888536436158499 12728317300332804654237749)
              ·
                refine ⟨1193279746906200436334789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12728317300332804654237749 1193279746906200436334789)
                ·
                  refine ⟨223739952544912581812773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1193279746906200436334789 223739952544912581812773)
                  ·
                    rfl

theorem cell22_1960794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_1960794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960794 prefixEnd_1960794 := by exact prefixLift 1960794
  have htrace : WordTrace (prefixWord ++ tailWord_1960794) baseStart_1960794 baseEnd_1960794 := by
    simpa [prefixWord, tailWord_1960794, baseEnd_1960794] using wordTrace_append hprefix tailTrace_1960794
  have hstable : (prefixWord ++ tailWord_1960794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960794).length < 2 ^ (prefixWord ++ tailWord_1960794).sum := by decide
  have hdescent : baseEnd_1960794 < baseStart_1960794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960796 : List Nat := [2, 2, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1960796 : Nat := 118140960795 + 1960796 * 2 ^ 59
def prefixEnd_1960796 : Nat := 4983230072969 + 3 ^ 40 * 1960796 * 2
def baseEnd_1960796 : Nat := 671220542275610406888313

theorem tailTrace_1960796 : CollatzResearch.WordTrace tailWord_1960796 prefixEnd_1960796 671220542275610406888313 := by
  unfold tailWord_1960796
  simp only [CollatzResearch.WordTrace]
  refine ⟨35758052702189222070483121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47677403602918962760644161 35758052702189222070483121)
  ·
    refine ⟨26818539526641916552862341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35758052702189222070483121 26818539526641916552862341)
    ·
      refine ⟨5028476161245359353661689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26818539526641916552862341 5028476161245359353661689)
      ·
        refine ⟨3771357120934019515246267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5028476161245359353661689 3771357120934019515246267)
        ·
          refine ⟨5657035681401029272869401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3771357120934019515246267 5657035681401029272869401)
          ·
            refine ⟨4242776761050771954652051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5657035681401029272869401 4242776761050771954652051)
            ·
              refine ⟨6364165141576157931978077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4242776761050771954652051 6364165141576157931978077)
              ·
                refine ⟨2386561928091059224491779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6364165141576157931978077 2386561928091059224491779)
                ·
                  refine ⟨3579842892136588836737669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2386561928091059224491779 3579842892136588836737669)
                  ·
                    refine ⟨671220542275610406888313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3579842892136588836737669 671220542275610406888313)
                    ·
                      rfl

theorem cell22_1960796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1960796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960796 prefixEnd_1960796 := by exact prefixLift 1960796
  have htrace : WordTrace (prefixWord ++ tailWord_1960796) baseStart_1960796 baseEnd_1960796 := by
    simpa [prefixWord, tailWord_1960796, baseEnd_1960796] using wordTrace_append hprefix tailTrace_1960796
  have hstable : (prefixWord ++ tailWord_1960796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960796).length < 2 ^ (prefixWord ++ tailWord_1960796).sum := by decide
  have hdescent : baseEnd_1960796 < baseStart_1960796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960839 : List Nat := [1, 1, 4, 2, 3, 1, 4, 6]
def baseStart_1960839 : Nat := 118140960795 + 1960839 * 2 ^ 59
def prefixEnd_1960839 : Nat := 4983230072969 + 3 ^ 40 * 1960839 * 2
def baseEnd_1960839 : Nat := 74581695783819180895909

theorem tailTrace_1960839 : CollatzResearch.WordTrace tailWord_1960839 prefixEnd_1960839 74581695783819180895909 := by
  unfold tailWord_1960839
  simp only [CollatzResearch.WordTrace]
  refine ⟨71517673743222662484781571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47678449162148441656521047 71517673743222662484781571)
  ·
    refine ⟨107276510614833993727172357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71517673743222662484781571 107276510614833993727172357)
    ·
      refine ⟨20114345740281373823844817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107276510614833993727172357 20114345740281373823844817)
      ·
        refine ⟨15085759305211030367883613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20114345740281373823844817 15085759305211030367883613)
        ·
          refine ⟨5657159739454136387956355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15085759305211030367883613 5657159739454136387956355)
          ·
            refine ⟨8485739609181204581934533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5657159739454136387956355 8485739609181204581934533)
            ·
              refine ⟨1591076176721475859112725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8485739609181204581934533 1591076176721475859112725)
              ·
                refine ⟨74581695783819180895909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1591076176721475859112725 74581695783819180895909)
                ·
                  rfl

theorem cell22_1960839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 6].length) (baseStart_1960839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960839 prefixEnd_1960839 := by exact prefixLift 1960839
  have htrace : WordTrace (prefixWord ++ tailWord_1960839) baseStart_1960839 baseEnd_1960839 := by
    simpa [prefixWord, tailWord_1960839, baseEnd_1960839] using wordTrace_append hprefix tailTrace_1960839
  have hstable : (prefixWord ++ tailWord_1960839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960839).length < 2 ^ (prefixWord ++ tailWord_1960839).sum := by decide
  have hdescent : baseEnd_1960839 < baseStart_1960839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960867 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 7]
def baseStart_1960867 : Nat := 118140960795 + 1960867 * 2 ^ 59
def prefixEnd_1960867 : Nat := 4983230072969 + 3 ^ 40 * 1960867 * 2
def baseEnd_1960867 : Nat := 223748282342196629454365

theorem tailTrace_1960867 : CollatzResearch.WordTrace tailWord_1960867 prefixEnd_1960867 223748282342196629454365 := by
  unfold tailWord_1960867
  simp only [CollatzResearch.WordTrace]
  refine ⟨71518694987121223266800855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47679129991414148844533903 71518694987121223266800855)
  ·
    refine ⟨107278042480681834900201283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71518694987121223266800855 107278042480681834900201283)
    ·
      refine ⟨160917063721022752350301925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107278042480681834900201283 160917063721022752350301925)
      ·
        refine ⟨30171949447691766065681611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160917063721022752350301925 30171949447691766065681611)
        ·
          refine ⟨45257924171537649098522417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30171949447691766065681611 45257924171537649098522417)
          ·
            refine ⟨33943443128653236823891813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45257924171537649098522417 33943443128653236823891813)
            ·
              refine ⟨6364395586622481904479715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33943443128653236823891813 6364395586622481904479715)
              ·
                refine ⟨9546593379933722856719573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6364395586622481904479715 9546593379933722856719573)
                ·
                  refine ⟨223748282342196629454365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9546593379933722856719573 223748282342196629454365)
                  ·
                    rfl

theorem cell22_1960867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 7].length) (baseStart_1960867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960867 prefixEnd_1960867 := by exact prefixLift 1960867
  have htrace : WordTrace (prefixWord ++ tailWord_1960867) baseStart_1960867 baseEnd_1960867 := by
    simpa [prefixWord, tailWord_1960867, baseEnd_1960867] using wordTrace_append hprefix tailTrace_1960867
  have hstable : (prefixWord ++ tailWord_1960867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960867).length < 2 ^ (prefixWord ++ tailWord_1960867).sum := by decide
  have hdescent : baseEnd_1960867 < baseStart_1960867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960877 : List Nat := [1, 5, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_1960877 : Nat := 118140960795 + 1960877 * 2 ^ 59
def prefixEnd_1960877 : Nat := 4983230072969 + 3 ^ 40 * 1960877 * 2
def baseEnd_1960877 : Nat := 671248270230953195613065

theorem tailTrace_1960877 : CollatzResearch.WordTrace tailWord_1960877 prefixEnd_1960877 671248270230953195613065 := by
  unfold tailWord_1960877
  simp only [CollatzResearch.WordTrace]
  refine ⟨71519059717084994974664885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47679373144723329983109923 71519059717084994974664885)
  ·
    refine ⟨6704911848476718278874833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71519059717084994974664885 6704911848476718278874833)
    ·
      refine ⟨5028683886357538709156125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6704911848476718278874833 5028683886357538709156125)
      ·
        refine ⟨1885756457384077015933547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5028683886357538709156125 1885756457384077015933547)
        ·
          refine ⟨2828634686076115523900321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1885756457384077015933547 2828634686076115523900321)
          ·
            refine ⟨2121476014557086642925241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2828634686076115523900321 2121476014557086642925241)
            ·
              refine ⟨1591107010917814982193931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2121476014557086642925241 1591107010917814982193931)
              ·
                refine ⟨2386660516376722473290897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591107010917814982193931 2386660516376722473290897)
                ·
                  refine ⟨1789995387282541854968173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2386660516376722473290897 1789995387282541854968173)
                  ·
                    refine ⟨671248270230953195613065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1789995387282541854968173 671248270230953195613065)
                    ·
                      rfl

theorem cell22_1960877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_1960877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960877 prefixEnd_1960877 := by exact prefixLift 1960877
  have htrace : WordTrace (prefixWord ++ tailWord_1960877) baseStart_1960877 baseEnd_1960877 := by
    simpa [prefixWord, tailWord_1960877, baseEnd_1960877] using wordTrace_append hprefix tailTrace_1960877
  have hstable : (prefixWord ++ tailWord_1960877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960877).length < 2 ^ (prefixWord ++ tailWord_1960877).sum := by decide
  have hdescent : baseEnd_1960877 < baseStart_1960877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960918 : List Nat := [5, 2, 1, 1, 2, 2, 2, 2, 5]
def baseStart_1960918 : Nat := 118140960795 + 1960918 * 2 ^ 59
def prefixEnd_1960918 : Nat := 4983230072969 + 3 ^ 40 * 1960918 * 2
def baseEnd_1960918 : Nat := 223754101789614251779313

theorem tailTrace_1960918 : CollatzResearch.WordTrace tailWord_1960918 prefixEnd_1960918 223754101789614251779313 := by
  unfold tailWord_1960918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4470034694371028686056713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47680370073290972651271605 4470034694371028686056713)
  ·
    refine ⟨3352526020778271514542535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4470034694371028686056713 3352526020778271514542535)
    ·
      refine ⟨5028789031167407271813803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3352526020778271514542535 5028789031167407271813803)
      ·
        refine ⟨7543183546751110907720705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5028789031167407271813803 7543183546751110907720705)
        ·
          refine ⟨5657387660063333180790529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7543183546751110907720705 5657387660063333180790529)
          ·
            refine ⟨4243040745047499885592897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5657387660063333180790529 4243040745047499885592897)
            ·
              refine ⟨3182280558785624914194673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4243040745047499885592897 3182280558785624914194673)
              ·
                refine ⟨2386710419089218685646005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3182280558785624914194673 2386710419089218685646005)
                ·
                  refine ⟨223754101789614251779313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2386710419089218685646005 223754101789614251779313)
                  ·
                    rfl

theorem cell22_1960918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_1960918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960918 prefixEnd_1960918 := by exact prefixLift 1960918
  have htrace : WordTrace (prefixWord ++ tailWord_1960918) baseStart_1960918 baseEnd_1960918 := by
    simpa [prefixWord, tailWord_1960918, baseEnd_1960918] using wordTrace_append hprefix tailTrace_1960918
  have hstable : (prefixWord ++ tailWord_1960918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960918).length < 2 ^ (prefixWord ++ tailWord_1960918).sum := by decide
  have hdescent : baseEnd_1960918 < baseStart_1960918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960944 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 6, 3]
def baseStart_1960944 : Nat := 118140960795 + 1960944 * 2 ^ 59
def prefixEnd_1960944 : Nat := 4983230072969 + 3 ^ 40 * 1960944 * 2
def baseEnd_1960944 : Nat := 671271205700187354187859

theorem tailTrace_1960944 : CollatzResearch.WordTrace tailWord_1960944 prefixEnd_1960944 671271205700187354187859 := by
  unfold tailWord_1960944
  simp only [CollatzResearch.WordTrace]
  refine ⟨35760751703921132708676943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47681002271894843611569257 35760751703921132708676943)
  ·
    refine ⟨53641127555881699063015415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35760751703921132708676943 53641127555881699063015415)
    ·
      refine ⟨80461691333822548594523123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53641127555881699063015415 80461691333822548594523123)
      ·
        refine ⟨120692537000733822891784685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80461691333822548594523123 120692537000733822891784685)
        ·
          refine ⟨45259701375275183584419257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120692537000733822891784685 45259701375275183584419257)
          ·
            refine ⟨33944776031456387688314443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45259701375275183584419257 33944776031456387688314443)
            ·
              refine ⟨50917164047184581532471665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33944776031456387688314443 50917164047184581532471665)
              ·
                refine ⟨38187873035388436149353749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50917164047184581532471665 38187873035388436149353749)
                ·
                  refine ⟨1790056548533832944500957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38187873035388436149353749 1790056548533832944500957)
                  ·
                    refine ⟨671271205700187354187859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1790056548533832944500957 671271205700187354187859)
                    ·
                      rfl

theorem cell22_1960944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 6, 3].length) (baseStart_1960944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960944 prefixEnd_1960944 := by exact prefixLift 1960944
  have htrace : WordTrace (prefixWord ++ tailWord_1960944) baseStart_1960944 baseEnd_1960944 := by
    simpa [prefixWord, tailWord_1960944, baseEnd_1960944] using wordTrace_append hprefix tailTrace_1960944
  have hstable : (prefixWord ++ tailWord_1960944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960944).length < 2 ^ (prefixWord ++ tailWord_1960944).sum := by decide
  have hdescent : baseEnd_1960944 < baseStart_1960944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1960974 : List Nat := [4, 1, 1, 2, 2, 3, 9]
def baseStart_1960974 : Nat := 118140960795 + 1960974 * 2 ^ 59
def prefixEnd_1960974 : Nat := 4983230072969 + 3 ^ 40 * 1960974 * 2
def baseEnd_1960974 : Nat := 24862276863454713923621

theorem tailTrace_1960974 : CollatzResearch.WordTrace tailWord_1960974 prefixEnd_1960974 24862276863454713923621 := by
  unfold tailWord_1960974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8940324699716697567618247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47681731731822387027297317 8940324699716697567618247)
  ·
    refine ⟨13410487049575046351427371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8940324699716697567618247 13410487049575046351427371)
    ·
      refine ⟨20115730574362569527141057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13410487049575046351427371 20115730574362569527141057)
      ·
        refine ⟨15086797930771927145355793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20115730574362569527141057 15086797930771927145355793)
        ·
          refine ⟨11315098448078945359016845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15086797930771927145355793 11315098448078945359016845)
          ·
            refine ⟨4243161918029604509631317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11315098448078945359016845 4243161918029604509631317)
            ·
              refine ⟨24862276863454713923621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4243161918029604509631317 24862276863454713923621)
              ·
                rfl

theorem cell22_1960974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 9].length) (baseStart_1960974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1960974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1960974 prefixEnd_1960974 := by exact prefixLift 1960974
  have htrace : WordTrace (prefixWord ++ tailWord_1960974) baseStart_1960974 baseEnd_1960974 := by
    simpa [prefixWord, tailWord_1960974, baseEnd_1960974] using wordTrace_append hprefix tailTrace_1960974
  have hstable : (prefixWord ++ tailWord_1960974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1960974).length < 2 ^ (prefixWord ++ tailWord_1960974).sum := by decide
  have hdescent : baseEnd_1960974 < baseStart_1960974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1960974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961034 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_1961034 : Nat := 118140960795 + 1961034 * 2 ^ 59
def prefixEnd_1961034 : Nat := 4983230072969 + 3 ^ 40 * 1961034 * 2
def baseEnd_1961034 : Nat := 671302014539457119437583

theorem tailTrace_1961034 : CollatzResearch.WordTrace tailWord_1961034 prefixEnd_1961034 671302014539457119437583 := by
  unfold tailWord_1961034
  simp only [CollatzResearch.WordTrace]
  refine ⟨17881196494379052697032539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47683190651677473858753437 17881196494379052697032539)
  ·
    refine ⟨26821794741568579045548809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17881196494379052697032539 26821794741568579045548809)
    ·
      refine ⟨20116346056176434284161607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26821794741568579045548809 20116346056176434284161607)
      ·
        refine ⟨30174519084264651426242411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20116346056176434284161607 30174519084264651426242411)
        ·
          refine ⟨45261778626396977139363617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30174519084264651426242411 45261778626396977139363617)
          ·
            refine ⟨33946333969797732854522713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45261778626396977139363617 33946333969797732854522713)
            ·
              refine ⟨25459750477348299640892035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33946333969797732854522713 25459750477348299640892035)
              ·
                refine ⟨38189625716022449461338053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25459750477348299640892035 38189625716022449461338053)
                ·
                  refine ⟨7160554821754209274000885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38189625716022449461338053 7160554821754209274000885)
                  ·
                    refine ⟨671302014539457119437583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7160554821754209274000885 671302014539457119437583)
                    ·
                      rfl

theorem cell22_1961034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_1961034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961034 prefixEnd_1961034 := by exact prefixLift 1961034
  have htrace : WordTrace (prefixWord ++ tailWord_1961034) baseStart_1961034 baseEnd_1961034 := by
    simpa [prefixWord, tailWord_1961034, baseEnd_1961034] using wordTrace_append hprefix tailTrace_1961034
  have hstable : (prefixWord ++ tailWord_1961034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961034).length < 2 ^ (prefixWord ++ tailWord_1961034).sum := by decide
  have hdescent : baseEnd_1961034 < baseStart_1961034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961046 : List Nat := [5, 2, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_1961046 : Nat := 118140960795 + 1961046 * 2 ^ 59
def prefixEnd_1961046 : Nat := 4983230072969 + 3 ^ 40 * 1961046 * 2
def baseEnd_1961046 : Nat := 671306122384693088137547

theorem tailTrace_1961046 : CollatzResearch.WordTrace tailWord_1961046 prefixEnd_1961046 671306122384693088137547 := by
  unfold tailWord_1961046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4470326478342046052347937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47683482435648491225044661 4470326478342046052347937)
  ·
    refine ⟨3352744858756534539260953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4470326478342046052347937 3352744858756534539260953)
    ·
      refine ⟨2514558644067400904445715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3352744858756534539260953 2514558644067400904445715)
      ·
        refine ⟨3771837966101101356668573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2514558644067400904445715 3771837966101101356668573)
        ·
          refine ⟨1414439237287913008750715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3771837966101101356668573 1414439237287913008750715)
          ·
            refine ⟨2121658855931869513126073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414439237287913008750715 2121658855931869513126073)
            ·
              refine ⟨1591244141948902134844555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2121658855931869513126073 1591244141948902134844555)
              ·
                refine ⟨2386866212923353202266833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591244141948902134844555 2386866212923353202266833)
                ·
                  refine ⟨1790149659692514901700125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2386866212923353202266833 1790149659692514901700125)
                  ·
                    refine ⟨671306122384693088137547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1790149659692514901700125 671306122384693088137547)
                    ·
                      rfl

theorem cell22_1961046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_1961046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961046 prefixEnd_1961046 := by exact prefixLift 1961046
  have htrace : WordTrace (prefixWord ++ tailWord_1961046) baseStart_1961046 baseEnd_1961046 := by
    simpa [prefixWord, tailWord_1961046, baseEnd_1961046] using wordTrace_append hprefix tailTrace_1961046
  have hstable : (prefixWord ++ tailWord_1961046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961046).length < 2 ^ (prefixWord ++ tailWord_1961046).sum := by decide
  have hdescent : baseEnd_1961046 < baseStart_1961046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961098 : List Nat := [3, 1, 2, 3, 1, 1, 3, 4, 4]
def baseStart_1961098 : Nat := 118140960795 + 1961098 * 2 ^ 59
def prefixEnd_1961098 : Nat := 4983230072969 + 3 ^ 40 * 1961098 * 2
def baseEnd_1961098 : Nat := 223774641015794095279129

theorem tailTrace_1961098 : CollatzResearch.WordTrace tailWord_1961098 prefixEnd_1961098 223774641015794095279129 := by
  unfold tailWord_1961098
  simp only [CollatzResearch.WordTrace]
  refine ⟨17881780062321087429614987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47684746832856233145639965 17881780062321087429614987)
  ·
    refine ⟨26822670093481631144422481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17881780062321087429614987 26822670093481631144422481)
    ·
      refine ⟨20117002570111223358316861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26822670093481631144422481 20117002570111223358316861)
      ·
        refine ⟨7543875963791708759368823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20117002570111223358316861 7543875963791708759368823)
        ·
          refine ⟨11315813945687563139053235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7543875963791708759368823 11315813945687563139053235)
          ·
            refine ⟨16973720918531344708579853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11315813945687563139053235 16973720918531344708579853)
            ·
              refine ⟨6365145344449254265717445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16973720918531344708579853 6365145344449254265717445)
              ·
                refine ⟨1193464752084235174822021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6365145344449254265717445 1193464752084235174822021)
                ·
                  refine ⟨223774641015794095279129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1193464752084235174822021 223774641015794095279129)
                  ·
                    rfl

theorem cell22_1961098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_1961098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961098 prefixEnd_1961098 := by exact prefixLift 1961098
  have htrace : WordTrace (prefixWord ++ tailWord_1961098) baseStart_1961098 baseEnd_1961098 := by
    simpa [prefixWord, tailWord_1961098, baseEnd_1961098] using wordTrace_append hprefix tailTrace_1961098
  have hstable : (prefixWord ++ tailWord_1961098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961098).length < 2 ^ (prefixWord ++ tailWord_1961098).sum := by decide
  have hdescent : baseEnd_1961098 < baseStart_1961098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961109 : List Nat := [1, 3, 2, 1, 1, 1, 2, 11]
def baseStart_1961109 : Nat := 118140960795 + 1961109 * 2 ^ 59
def prefixEnd_1961109 : Nat := 4983230072969 + 3 ^ 40 * 1961109 * 2
def baseEnd_1961109 : Nat := 74591965396909102645817

theorem tailTrace_1961109 : CollatzResearch.WordTrace tailWord_1961109 prefixEnd_1961109 74591965396909102645817 := by
  unfold tailWord_1961109
  simp only [CollatzResearch.WordTrace]
  refine ⟨71527521452244498597110381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47685014301496332398073587 71527521452244498597110381)
  ·
    refine ⟨26822820544591686973916393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71527521452244498597110381 26822820544591686973916393)
    ·
      refine ⟨20117115408443765230437295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26822820544591686973916393 20117115408443765230437295)
      ·
        refine ⟨30175673112665647845655943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20117115408443765230437295 30175673112665647845655943)
        ·
          refine ⟨45263509668998471768483915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30175673112665647845655943 45263509668998471768483915)
          ·
            refine ⟨67895264503497707652725873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45263509668998471768483915 67895264503497707652725873)
            ·
              refine ⟨50921448377623280739544405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67895264503497707652725873 50921448377623280739544405)
              ·
                refine ⟨74591965396909102645817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 50921448377623280739544405 74591965396909102645817)
                ·
                  rfl

theorem cell22_1961109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 11].length) (baseStart_1961109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961109 prefixEnd_1961109 := by exact prefixLift 1961109
  have htrace : WordTrace (prefixWord ++ tailWord_1961109) baseStart_1961109 baseEnd_1961109 := by
    simpa [prefixWord, tailWord_1961109, baseEnd_1961109] using wordTrace_append hprefix tailTrace_1961109
  have hstable : (prefixWord ++ tailWord_1961109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961109).length < 2 ^ (prefixWord ++ tailWord_1961109).sum := by decide
  have hdescent : baseEnd_1961109 < baseStart_1961109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961201 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 5, 4]
def baseStart_1961201 : Nat := 118140960795 + 1961201 * 2 ^ 59
def prefixEnd_1961201 : Nat := 4983230072969 + 3 ^ 40 * 1961201 * 2
def baseEnd_1961201 : Nat := 671359182052324350512071

theorem tailTrace_1961201 : CollatzResearch.WordTrace tailWord_1961201 prefixEnd_1961201 671359182052324350512071 := by
  unfold tailWord_1961201
  simp only [CollatzResearch.WordTrace]
  refine ⟨71530876967911198309459457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47687251311940798872972971 71530876967911198309459457)
  ·
    refine ⟨53648157725933398732094593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71530876967911198309459457 53648157725933398732094593)
    ·
      refine ⟨40236118294450049049070945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53648157725933398732094593 40236118294450049049070945)
      ·
        refine ⟨30177088720837536786803209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40236118294450049049070945 30177088720837536786803209)
        ·
          refine ⟨22632816540628152590102407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30177088720837536786803209 22632816540628152590102407)
          ·
            refine ⟨33949224810942228885153611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22632816540628152590102407 33949224810942228885153611)
            ·
              refine ⟨50923837216413343327730417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33949224810942228885153611 50923837216413343327730417)
              ·
                refine ⟨38192877912310007495797813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50923837216413343327730417 38192877912310007495797813)
                ·
                  refine ⟨3580582304279063202731045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38192877912310007495797813 3580582304279063202731045)
                  ·
                    refine ⟨671359182052324350512071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3580582304279063202731045 671359182052324350512071)
                    ·
                      rfl

theorem cell22_1961201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 4].length) (baseStart_1961201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961201 prefixEnd_1961201 := by exact prefixLift 1961201
  have htrace : WordTrace (prefixWord ++ tailWord_1961201) baseStart_1961201 baseEnd_1961201 := by
    simpa [prefixWord, tailWord_1961201, baseEnd_1961201] using wordTrace_append hprefix tailTrace_1961201
  have hstable : (prefixWord ++ tailWord_1961201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961201).length < 2 ^ (prefixWord ++ tailWord_1961201).sum := by decide
  have hdescent : baseEnd_1961201 < baseStart_1961201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961265 : List Nat := [1, 2, 2, 3, 3, 1, 1, 4, 2, 3]
def baseStart_1961265 : Nat := 118140960795 + 1961265 * 2 ^ 59
def prefixEnd_1961265 : Nat := 4983230072969 + 3 ^ 40 * 1961265 * 2
def baseEnd_1961265 : Nat := 671381090560249516911875

theorem tailTrace_1961265 : CollatzResearch.WordTrace tailWord_1961265 prefixEnd_1961265 671381090560249516911875 := by
  unfold tailWord_1961265
  simp only [CollatzResearch.WordTrace]
  refine ⟨71533211239679337239789249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47688807493119558159859499 71533211239679337239789249)
  ·
    refine ⟨53649908429759502929841937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71533211239679337239789249 53649908429759502929841937)
    ·
      refine ⟨40237431322319627197381453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53649908429759502929841937 40237431322319627197381453)
      ·
        refine ⟨15089036745869860199018045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40237431322319627197381453 15089036745869860199018045)
        ·
          refine ⟨5658388779701197574631767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15089036745869860199018045 5658388779701197574631767)
          ·
            refine ⟨8487583169551796361947651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5658388779701197574631767 8487583169551796361947651)
            ·
              refine ⟨12731374754327694542921477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8487583169551796361947651 12731374754327694542921477)
              ·
                refine ⟨2387132766436442726797777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12731374754327694542921477 2387132766436442726797777)
                ·
                  refine ⟨1790349574827332045098333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2387132766436442726797777 1790349574827332045098333)
                  ·
                    refine ⟨671381090560249516911875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1790349574827332045098333 671381090560249516911875)
                    ·
                      rfl

theorem cell22_1961265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_1961265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961265 prefixEnd_1961265 := by exact prefixLift 1961265
  have htrace : WordTrace (prefixWord ++ tailWord_1961265) baseStart_1961265 baseEnd_1961265 := by
    simpa [prefixWord, tailWord_1961265, baseEnd_1961265] using wordTrace_append hprefix tailTrace_1961265
  have hstable : (prefixWord ++ tailWord_1961265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961265).length < 2 ^ (prefixWord ++ tailWord_1961265).sum := by decide
  have hdescent : baseEnd_1961265 < baseStart_1961265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961267 : List Nat := [1, 1, 1, 2, 5, 4, 2, 2, 4]
def baseStart_1961267 : Nat := 118140960795 + 1961267 * 2 ^ 59
def prefixEnd_1961267 : Nat := 4983230072969 + 3 ^ 40 * 1961267 * 2
def baseEnd_1961267 : Nat := 223793925067040726120623

theorem tailTrace_1961267 : CollatzResearch.WordTrace tailWord_1961267 prefixEnd_1961267 223793925067040726120623 := by
  unfold tailWord_1961267
  simp only [CollatzResearch.WordTrace]
  refine ⟨71533284185672091581362055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47688856123781394387574703 71533284185672091581362055)
  ·
    refine ⟨107299926278508137372043083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71533284185672091581362055 107299926278508137372043083)
    ·
      refine ⟨160949889417762206058064625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107299926278508137372043083 160949889417762206058064625)
      ·
        refine ⟨120712417063321654543548469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160949889417762206058064625 120712417063321654543548469)
        ·
          refine ⟨11316789099686405113457669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120712417063321654543548469 11316789099686405113457669)
          ·
            refine ⟨2121897956191200958773313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11316789099686405113457669 2121897956191200958773313)
            ·
              refine ⟨1591423467143400719079985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2121897956191200958773313 1591423467143400719079985)
              ·
                refine ⟨1193567600357550539309989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1591423467143400719079985 1193567600357550539309989)
                ·
                  refine ⟨223793925067040726120623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1193567600357550539309989 223793925067040726120623)
                  ·
                    rfl

theorem cell22_1961267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 4].length) (baseStart_1961267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961267 prefixEnd_1961267 := by exact prefixLift 1961267
  have htrace : WordTrace (prefixWord ++ tailWord_1961267) baseStart_1961267 baseEnd_1961267 := by
    simpa [prefixWord, tailWord_1961267, baseEnd_1961267] using wordTrace_append hprefix tailTrace_1961267
  have hstable : (prefixWord ++ tailWord_1961267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961267).length < 2 ^ (prefixWord ++ tailWord_1961267).sum := by decide
  have hdescent : baseEnd_1961267 < baseStart_1961267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961340 : List Nat := [2, 2, 2, 1, 1, 1, 7, 1, 5]
def baseStart_1961340 : Nat := 118140960795 + 1961340 * 2 ^ 59
def prefixEnd_1961340 : Nat := 4983230072969 + 3 ^ 40 * 1961340 * 2
def baseEnd_1961340 : Nat := 223802254864324773762215

theorem tailTrace_1961340 : CollatzResearch.WordTrace tailWord_1961340 prefixEnd_1961340 223802254864324773762215 := by
  unfold tailWord_1961340
  simp only [CollatzResearch.WordTrace]
  refine ⟨35767973357203812524384737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47690631142938416699179649 35767973357203812524384737)
  ·
    refine ⟨26825980017902859393288553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35767973357203812524384737 26825980017902859393288553)
    ·
      refine ⟨20119485013427144544966415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26825980017902859393288553 20119485013427144544966415)
      ·
        refine ⟨30179227520140716817449623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20119485013427144544966415 30179227520140716817449623)
        ·
          refine ⟨45268841280211075226174435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30179227520140716817449623 45268841280211075226174435)
          ·
            refine ⟨67903261920316612839261653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45268841280211075226174435 67903261920316612839261653)
            ·
              refine ⟨1591482701257420613420195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 67903261920316612839261653 1591482701257420613420195)
              ·
                refine ⟨2387224051886130920130293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591482701257420613420195 2387224051886130920130293)
                ·
                  refine ⟨223802254864324773762215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2387224051886130920130293 223802254864324773762215)
                  ·
                    rfl

theorem cell22_1961340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_1961340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961340 prefixEnd_1961340 := by exact prefixLift 1961340
  have htrace : WordTrace (prefixWord ++ tailWord_1961340) baseStart_1961340 baseEnd_1961340 := by
    simpa [prefixWord, tailWord_1961340, baseEnd_1961340] using wordTrace_append hprefix tailTrace_1961340
  have hstable : (prefixWord ++ tailWord_1961340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961340).length < 2 ^ (prefixWord ++ tailWord_1961340).sum := by decide
  have hdescent : baseEnd_1961340 < baseStart_1961340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961370 : List Nat := [3, 1, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_1961370 : Nat := 118140960795 + 1961370 * 2 ^ 59
def prefixEnd_1961370 : Nat := 4983230072969 + 3 ^ 40 * 1961370 * 2
def baseEnd_1961370 : Nat := 671417034206064243036553

theorem tailTrace_1961370 : CollatzResearch.WordTrace tailWord_1961370 prefixEnd_1961370 671417034206064243036553 := by
  unfold tailWord_1961370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17884260226074735043090391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47691360602865960114907709 17884260226074735043090391)
  ·
    refine ⟨26826390339112102564635587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17884260226074735043090391 26826390339112102564635587)
    ·
      refine ⟨40239585508668153846953381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26826390339112102564635587 40239585508668153846953381)
      ·
        refine ⟨7544922282875278846303759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40239585508668153846953381 7544922282875278846303759)
        ·
          refine ⟨11317383424312918269455639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7544922282875278846303759 11317383424312918269455639)
          ·
            refine ⟨16976075136469377404183459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11317383424312918269455639 16976075136469377404183459)
            ·
              refine ⟨25464112704704066106275189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16976075136469377404183459 25464112704704066106275189)
              ·
                refine ⟨2387260566066006197463299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25464112704704066106275189 2387260566066006197463299)
                ·
                  refine ⟨3580890849099009296194949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387260566066006197463299 3580890849099009296194949)
                  ·
                    refine ⟨671417034206064243036553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3580890849099009296194949 671417034206064243036553)
                    ·
                      rfl

theorem cell22_1961370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_1961370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961370 prefixEnd_1961370 := by exact prefixLift 1961370
  have htrace : WordTrace (prefixWord ++ tailWord_1961370) baseStart_1961370 baseEnd_1961370 := by
    simpa [prefixWord, tailWord_1961370, baseEnd_1961370] using wordTrace_append hprefix tailTrace_1961370
  have hstable : (prefixWord ++ tailWord_1961370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961370).length < 2 ^ (prefixWord ++ tailWord_1961370).sum := by decide
  have hdescent : baseEnd_1961370 < baseStart_1961370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961404 : List Nat := [2, 2, 2, 4, 2, 2, 1, 2, 1, 4]
def baseStart_1961404 : Nat := 118140960795 + 1961404 * 2 ^ 59
def prefixEnd_1961404 : Nat := 4983230072969 + 3 ^ 40 * 1961404 * 2
def baseEnd_1961404 : Nat := 671428673100899487686449

theorem tailTrace_1961404 : CollatzResearch.WordTrace tailWord_1961404 prefixEnd_1961404 671428673100899487686449 := by
  unfold tailWord_1961404
  simp only [CollatzResearch.WordTrace]
  refine ⟨35769140493087881989549633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47692187324117175986066177 35769140493087881989549633)
  ·
    refine ⟨26826855369815911492162225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35769140493087881989549633 26826855369815911492162225)
    ·
      refine ⟨20120141527361933619121669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26826855369815911492162225 20120141527361933619121669)
      ·
        refine ⟨3772526536380362553585313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20120141527361933619121669 3772526536380362553585313)
        ·
          refine ⟨2829394902285271915188985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3772526536380362553585313 2829394902285271915188985)
          ·
            refine ⟨2122046176713953936391739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2829394902285271915188985 2122046176713953936391739)
            ·
              refine ⟨3183069265070930904587609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122046176713953936391739 3183069265070930904587609)
              ·
                refine ⟨2387301948803198178440707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3183069265070930904587609 2387301948803198178440707)
                ·
                  refine ⟨3580952923204797267661061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2387301948803198178440707 3580952923204797267661061)
                  ·
                    refine ⟨671428673100899487686449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3580952923204797267661061 671428673100899487686449)
                    ·
                      rfl

theorem cell22_1961404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_1961404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961404 prefixEnd_1961404 := by exact prefixLift 1961404
  have htrace : WordTrace (prefixWord ++ tailWord_1961404) baseStart_1961404 baseEnd_1961404 := by
    simpa [prefixWord, tailWord_1961404, baseEnd_1961404] using wordTrace_append hprefix tailTrace_1961404
  have hstable : (prefixWord ++ tailWord_1961404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961404).length < 2 ^ (prefixWord ++ tailWord_1961404).sum := by decide
  have hdescent : baseEnd_1961404 < baseStart_1961404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961415 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 2, 4]
def baseStart_1961415 : Nat := 118140960795 + 1961415 * 2 ^ 59
def prefixEnd_1961415 : Nat := 4983230072969 + 3 ^ 40 * 1961415 * 2
def baseEnd_1961415 : Nat := 671432438625699125661415

theorem tailTrace_1961415 : CollatzResearch.WordTrace tailWord_1961415 prefixEnd_1961415 671432438625699125661415 := by
  unfold tailWord_1961415
  simp only [CollatzResearch.WordTrace]
  refine ⟨71538682189135912857749699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47692454792757275238499799 71538682189135912857749699)
  ·
    refine ⟨107308023283703869286624549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71538682189135912857749699 107308023283703869286624549)
    ·
      refine ⟨20120254365694475491242103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107308023283703869286624549 20120254365694475491242103)
      ·
        refine ⟨30180381548541713236863155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20120254365694475491242103 30180381548541713236863155)
        ·
          refine ⟨45270572322812569855294733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30180381548541713236863155 45270572322812569855294733)
          ·
            refine ⟨16976464621054713695735525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45270572322812569855294733 16976464621054713695735525)
            ·
              refine ⟨3183087116447758817950411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16976464621054713695735525 3183087116447758817950411)
              ·
                refine ⟨4774630674671638226925617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183087116447758817950411 4774630674671638226925617)
                ·
                  refine ⟨3580973006003728670194213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4774630674671638226925617 3580973006003728670194213)
                  ·
                    refine ⟨671432438625699125661415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3580973006003728670194213 671432438625699125661415)
                    ·
                      rfl

theorem cell22_1961415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_1961415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961415 prefixEnd_1961415 := by exact prefixLift 1961415
  have htrace : WordTrace (prefixWord ++ tailWord_1961415) baseStart_1961415 baseEnd_1961415 := by
    simpa [prefixWord, tailWord_1961415, baseEnd_1961415] using wordTrace_append hprefix tailTrace_1961415
  have hstable : (prefixWord ++ tailWord_1961415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961415).length < 2 ^ (prefixWord ++ tailWord_1961415).sum := by decide
  have hdescent : baseEnd_1961415 < baseStart_1961415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961430 : List Nat := [5, 2, 1, 1, 1, 12]
def baseStart_1961430 : Nat := 118140960795 + 1961430 * 2 ^ 59
def prefixEnd_1961430 : Nat := 4983230072969 + 3 ^ 40 * 1961430 * 2
def baseEnd_1961430 : Nat := 8289352758422766500449

theorem tailTrace_1961430 : CollatzResearch.WordTrace tailWord_1961430 prefixEnd_1961430 8289352758422766500449 := by
  unfold tailWord_1961430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4471201830255098151221609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47692819522721046946363829 4471201830255098151221609)
  ·
    refine ⟨3353401372691323613416207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4471201830255098151221609 3353401372691323613416207)
    ·
      refine ⟨5030102059036985420124311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3353401372691323613416207 5030102059036985420124311)
      ·
        refine ⟨7545153088555478130186467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5030102059036985420124311 7545153088555478130186467)
        ·
          refine ⟨11317729632833217195279701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7545153088555478130186467 11317729632833217195279701)
          ·
            refine ⟨8289352758422766500449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 11317729632833217195279701 8289352758422766500449)
            ·
              rfl

theorem cell22_1961430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 12].length) (baseStart_1961430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961430 prefixEnd_1961430 := by exact prefixLift 1961430
  have htrace : WordTrace (prefixWord ++ tailWord_1961430) baseStart_1961430 baseEnd_1961430 := by
    simpa [prefixWord, tailWord_1961430, baseEnd_1961430] using wordTrace_append hprefix tailTrace_1961430
  have hstable : (prefixWord ++ tailWord_1961430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961430).length < 2 ^ (prefixWord ++ tailWord_1961430).sum := by decide
  have hdescent : baseEnd_1961430 < baseStart_1961430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961462 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_1961462 : Nat := 118140960795 + 1961462 * 2 ^ 59
def prefixEnd_1961462 : Nat := 4983230072969 + 3 ^ 40 * 1961462 * 2
def baseEnd_1961462 : Nat := 671448527686206669736271

theorem tailTrace_1961462 : CollatzResearch.WordTrace tailWord_1961462 prefixEnd_1961462 671448527686206669736271 := by
  unfold tailWord_1961462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4471274776247852492794415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47693597613310426589807093 4471274776247852492794415)
  ·
    refine ⟨6706912164371778739191623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4471274776247852492794415 6706912164371778739191623)
    ·
      refine ⟨10060368246557668108787435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6706912164371778739191623 10060368246557668108787435)
      ·
        refine ⟨15090552369836502163181153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10060368246557668108787435 15090552369836502163181153)
        ·
          refine ⟨11317914277377376622385865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15090552369836502163181153 11317914277377376622385865)
          ·
            refine ⟨8488435708033032466789399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11317914277377376622385865 8488435708033032466789399)
            ·
              refine ⟨12732653562049548700184099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8488435708033032466789399 12732653562049548700184099)
              ·
                refine ⟨19098980343074323050276149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12732653562049548700184099 19098980343074323050276149)
                ·
                  refine ⟨1790529407163217785963389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19098980343074323050276149 1790529407163217785963389)
                  ·
                    refine ⟨671448527686206669736271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1790529407163217785963389 671448527686206669736271)
                    ·
                      rfl

theorem cell22_1961462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_1961462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961462 prefixEnd_1961462 := by exact prefixLift 1961462
  have htrace : WordTrace (prefixWord ++ tailWord_1961462) baseStart_1961462 baseEnd_1961462 := by
    simpa [prefixWord, tailWord_1961462, baseEnd_1961462] using wordTrace_append hprefix tailTrace_1961462
  have hstable : (prefixWord ++ tailWord_1961462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961462).length < 2 ^ (prefixWord ++ tailWord_1961462).sum := by decide
  have hdescent : baseEnd_1961462 < baseStart_1961462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961479 : List Nat := [1, 1, 4, 3, 2, 1, 1, 5, 1, 3]
def baseStart_1961479 : Nat := 118140960795 + 1961479 * 2 ^ 59
def prefixEnd_1961479 : Nat := 4983230072969 + 3 ^ 40 * 1961479 * 2
def baseEnd_1961479 : Nat := 671454347133624292061219

theorem tailTrace_1961479 : CollatzResearch.WordTrace tailWord_1961479 prefixEnd_1961479 671454347133624292061219 := by
  unfold tailWord_1961479
  simp only [CollatzResearch.WordTrace]
  refine ⟨71541016460904051788079491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47694010973936034525386327 71541016460904051788079491)
  ·
    refine ⟨107311524691356077682119237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71541016460904051788079491 107311524691356077682119237)
    ·
      refine ⟨20120910879629264565397357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107311524691356077682119237 20120910879629264565397357)
      ·
        refine ⟨7545341579860974212024009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20120910879629264565397357 7545341579860974212024009)
        ·
          refine ⟨5659006184895730659018007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7545341579860974212024009 5659006184895730659018007)
          ·
            refine ⟨8488509277343595988527011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5659006184895730659018007 8488509277343595988527011)
            ·
              refine ⟨12732763916015393982790517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8488509277343595988527011 12732763916015393982790517)
              ·
                refine ⟨1193696617126443185886611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12732763916015393982790517 1193696617126443185886611)
                ·
                  refine ⟨1790544925689664778829917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1193696617126443185886611 1790544925689664778829917)
                  ·
                    refine ⟨671454347133624292061219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1790544925689664778829917 671454347133624292061219)
                    ·
                      rfl

theorem cell22_1961479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_1961479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961479 prefixEnd_1961479 := by exact prefixLift 1961479
  have htrace : WordTrace (prefixWord ++ tailWord_1961479) baseStart_1961479 baseEnd_1961479 := by
    simpa [prefixWord, tailWord_1961479, baseEnd_1961479] using wordTrace_append hprefix tailTrace_1961479
  have hstable : (prefixWord ++ tailWord_1961479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961479).length < 2 ^ (prefixWord ++ tailWord_1961479).sum := by decide
  have hdescent : baseEnd_1961479 < baseStart_1961479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961485 : List Nat := [1, 7, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1961485 : Nat := 118140960795 + 1961485 * 2 ^ 59
def prefixEnd_1961485 : Nat := 4983230072969 + 3 ^ 40 * 1961485 * 2
def baseEnd_1961485 : Nat := 671456401056242276411201

theorem tailTrace_1961485 : CollatzResearch.WordTrace tailWord_1961485 prefixEnd_1961485 671456401056242276411201 := by
  unfold tailWord_1961485
  simp only [CollatzResearch.WordTrace]
  refine ⟨71541235298882314812797909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47694156865921543208531939 71541235298882314812797909)
  ·
    refine ⟨1676747702317554253424951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 71541235298882314812797909 1676747702317554253424951)
    ·
      refine ⟨2515121553476331380137427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1676747702317554253424951 2515121553476331380137427)
      ·
        refine ⟨3772682330214497070206141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2515121553476331380137427 3772682330214497070206141)
        ·
          refine ⟨1414755873830436401327303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3772682330214497070206141 1414755873830436401327303)
          ·
            refine ⟨2122133810745654601990955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1414755873830436401327303 2122133810745654601990955)
            ·
              refine ⟨3183200716118481902986433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2122133810745654601990955 3183200716118481902986433)
              ·
                refine ⟨2387400537088861427239825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3183200716118481902986433 2387400537088861427239825)
                ·
                  refine ⟨1790550402816646070429869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2387400537088861427239825 1790550402816646070429869)
                  ·
                    refine ⟨671456401056242276411201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1790550402816646070429869 671456401056242276411201)
                    ·
                      rfl

theorem cell22_1961485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1961485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961485 prefixEnd_1961485 := by exact prefixLift 1961485
  have htrace : WordTrace (prefixWord ++ tailWord_1961485) baseStart_1961485 baseEnd_1961485 := by
    simpa [prefixWord, tailWord_1961485, baseEnd_1961485] using wordTrace_append hprefix tailTrace_1961485
  have hstable : (prefixWord ++ tailWord_1961485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961485).length < 2 ^ (prefixWord ++ tailWord_1961485).sum := by decide
  have hdescent : baseEnd_1961485 < baseStart_1961485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961552 : List Nat := [2, 1, 1, 1, 1, 3, 4, 4, 2, 3]
def baseStart_1961552 : Nat := 118140960795 + 1961552 * 2 ^ 59
def prefixEnd_1961552 : Nat := 4983230072969 + 3 ^ 40 * 1961552 * 2
def baseEnd_1961552 : Nat := 671479336525476434985995

theorem tailTrace_1961552 : CollatzResearch.WordTrace tailWord_1961552 prefixEnd_1961552 671479336525476434985995 := by
  unfold tailWord_1961552
  simp only [CollatzResearch.WordTrace]
  refine ⟨35771839494819792627743455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47695785993093056836991273 35771839494819792627743455)
  ·
    refine ⟨53657759242229688941615183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35771839494819792627743455 53657759242229688941615183)
    ·
      refine ⟨80486638863344533412422775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53657759242229688941615183 80486638863344533412422775)
      ·
        refine ⟨120729958295016800118634163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80486638863344533412422775 120729958295016800118634163)
        ·
          refine ⟨181094937442525200177951245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120729958295016800118634163 181094937442525200177951245)
          ·
            refine ⟨67910601540946950066731717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181094937442525200177951245 67910601540946950066731717)
            ·
              refine ⟨12733237788927553137512197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67910601540946950066731717 12733237788927553137512197)
              ·
                refine ⟨2387482085423916213283537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12733237788927553137512197 2387482085423916213283537)
                ·
                  refine ⟨1790611564067937159962653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2387482085423916213283537 1790611564067937159962653)
                  ·
                    refine ⟨671479336525476434985995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1790611564067937159962653 671479336525476434985995)
                    ·
                      rfl

theorem cell22_1961552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 2, 3].length) (baseStart_1961552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961552 prefixEnd_1961552 := by exact prefixLift 1961552
  have htrace : WordTrace (prefixWord ++ tailWord_1961552) baseStart_1961552 baseEnd_1961552 := by
    simpa [prefixWord, tailWord_1961552, baseEnd_1961552] using wordTrace_append hprefix tailTrace_1961552
  have hstable : (prefixWord ++ tailWord_1961552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961552).length < 2 ^ (prefixWord ++ tailWord_1961552).sum := by decide
  have hdescent : baseEnd_1961552 < baseStart_1961552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961631 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 3, 3]
def baseStart_1961631 : Nat := 118140960795 + 1961631 * 2 ^ 59
def prefixEnd_1961631 : Nat := 4983230072969 + 3 ^ 40 * 1961631 * 2
def baseEnd_1961631 : Nat := 671506379839946562260753

theorem tailTrace_1961631 : CollatzResearch.WordTrace tailWord_1961631 prefixEnd_1961631 671506379839946562260753 := by
  unfold tailWord_1961631
  simp only [CollatzResearch.WordTrace]
  refine ⟨71546560356353381747612747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47697706904235587831741831 71546560356353381747612747)
  ·
    refine ⟨107319840534530072621419121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71546560356353381747612747 107319840534530072621419121)
    ·
      refine ⟨80489880400897554466064341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107319840534530072621419121 80489880400897554466064341)
      ·
        refine ⟨1886481571896036432798383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 80489880400897554466064341 1886481571896036432798383)
        ·
          refine ⟨2829722357844054649197575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1886481571896036432798383 2829722357844054649197575)
          ·
            refine ⟨4244583536766081973796363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2829722357844054649197575 4244583536766081973796363)
            ·
              refine ⟨6366875305149122960694545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4244583536766081973796363 6366875305149122960694545)
              ·
                refine ⟨4775156478861842220520909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6366875305149122960694545 4775156478861842220520909)
                ·
                  refine ⟨1790683679573190832695341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4775156478861842220520909 1790683679573190832695341)
                  ·
                    refine ⟨671506379839946562260753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1790683679573190832695341 671506379839946562260753)
                    ·
                      rfl

theorem cell22_1961631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 3].length) (baseStart_1961631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961631 prefixEnd_1961631 := by exact prefixLift 1961631
  have htrace : WordTrace (prefixWord ++ tailWord_1961631) baseStart_1961631 baseEnd_1961631 := by
    simpa [prefixWord, tailWord_1961631, baseEnd_1961631] using wordTrace_append hprefix tailTrace_1961631
  have hstable : (prefixWord ++ tailWord_1961631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961631).length < 2 ^ (prefixWord ++ tailWord_1961631).sum := by decide
  have hdescent : baseEnd_1961631 < baseStart_1961631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961672 : List Nat := [2, 1, 3, 1, 2, 2, 4, 1, 6]
def baseStart_1961672 : Nat := 118140960795 + 1961672 * 2 ^ 59
def prefixEnd_1961672 : Nat := 4983230072969 + 3 ^ 40 * 1961672 * 2
def baseEnd_1961672 : Nat := 223840138325945373995209

theorem tailTrace_1961672 : CollatzResearch.WordTrace tailWord_1961672 prefixEnd_1961672 223840138325945373995209 := by
  unfold tailWord_1961672
  simp only [CollatzResearch.WordTrace]
  refine ⟨35774027874602422874927635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47698703832803230499903513 35774027874602422874927635)
  ·
    refine ⟨53661041811903634312391453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35774027874602422874927635 53661041811903634312391453)
    ·
      refine ⟨20122890679463862867146795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53661041811903634312391453 20122890679463862867146795)
      ·
        refine ⟨30184336019195794300720193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20122890679463862867146795 30184336019195794300720193)
        ·
          refine ⟨22638252014396845725540145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30184336019195794300720193 22638252014396845725540145)
          ·
            refine ⟨16978689010797634294155109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22638252014396845725540145 16978689010797634294155109)
            ·
              refine ⟨3183504189524556430154083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16978689010797634294155109 3183504189524556430154083)
              ·
                refine ⟨4775256284286834645231125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3183504189524556430154083 4775256284286834645231125)
                ·
                  refine ⟨223840138325945373995209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4775256284286834645231125 223840138325945373995209)
                  ·
                    rfl

theorem cell22_1961672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 6].length) (baseStart_1961672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961672 prefixEnd_1961672 := by exact prefixLift 1961672
  have htrace : WordTrace (prefixWord ++ tailWord_1961672) baseStart_1961672 baseEnd_1961672 := by
    simpa [prefixWord, tailWord_1961672, baseEnd_1961672] using wordTrace_append hprefix tailTrace_1961672
  have hstable : (prefixWord ++ tailWord_1961672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961672).length < 2 ^ (prefixWord ++ tailWord_1961672).sum := by decide
  have hdescent : baseEnd_1961672 < baseStart_1961672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961704 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 4, 3]
def baseStart_1961704 : Nat := 118140960795 + 1961704 * 2 ^ 59
def prefixEnd_1961704 : Nat := 4983230072969 + 3 ^ 40 * 1961704 * 2
def baseEnd_1961704 : Nat := 671531369231798705185529

theorem tailTrace_1961704 : CollatzResearch.WordTrace tailWord_1961704 prefixEnd_1961704 671531369231798705185529 := by
  unfold tailWord_1961704
  simp only [CollatzResearch.WordTrace]
  refine ⟨35774611442544457607510083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47699481923392610143346777 35774611442544457607510083)
  ·
    refine ⟨53661917163816686411265125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35774611442544457607510083 53661917163816686411265125)
    ·
      refine ⟨10061609468215628702112211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53661917163816686411265125 10061609468215628702112211)
      ·
        refine ⟨15092414202323443053168317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10061609468215628702112211 15092414202323443053168317)
        ·
          refine ⟨5659655325871291144938119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15092414202323443053168317 5659655325871291144938119)
          ·
            refine ⟨8489482988806936717407179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5659655325871291144938119 8489482988806936717407179)
            ·
              refine ⟨12734224483210405076110769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8489482988806936717407179 12734224483210405076110769)
              ·
                refine ⟨9550668362407803807083077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12734224483210405076110769 9550668362407803807083077)
                ·
                  refine ⟨1790750317951463213828077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9550668362407803807083077 1790750317951463213828077)
                  ·
                    refine ⟨671531369231798705185529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1790750317951463213828077 671531369231798705185529)
                    ·
                      rfl

theorem cell22_1961704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_1961704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961704 prefixEnd_1961704 := by exact prefixLift 1961704
  have htrace : WordTrace (prefixWord ++ tailWord_1961704) baseStart_1961704 baseEnd_1961704 := by
    simpa [prefixWord, tailWord_1961704, baseEnd_1961704] using wordTrace_append hprefix tailTrace_1961704
  have hstable : (prefixWord ++ tailWord_1961704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961704).length < 2 ^ (prefixWord ++ tailWord_1961704).sum := by decide
  have hdescent : baseEnd_1961704 < baseStart_1961704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961738 : List Nat := [3, 1, 2, 2, 1, 5, 2, 1, 2, 3]
def baseStart_1961738 : Nat := 118140960795 + 1961738 * 2 ^ 59
def prefixEnd_1961738 : Nat := 4983230072969 + 3 ^ 40 * 1961738 * 2
def baseEnd_1961738 : Nat := 671543008126633949835425

theorem tailTrace_1961738 : CollatzResearch.WordTrace tailWord_1961738 prefixEnd_1961738 671543008126633949835425 := by
  unfold tailWord_1961738
  simp only [CollatzResearch.WordTrace]
  refine ⟨17887615741741434755439467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47700308644643826014505245 17887615741741434755439467)
  ·
    refine ⟨26831423612612152133159201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17887615741741434755439467 26831423612612152133159201)
    ·
      refine ⟨20123567709459114099869401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26831423612612152133159201 20123567709459114099869401)
      ·
        refine ⟨15092675782094335574902051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20123567709459114099869401 15092675782094335574902051)
        ·
          refine ⟨22639013673141503362353077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15092675782094335574902051 22639013673141503362353077)
          ·
            refine ⟨2122407531857015940220601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22639013673141503362353077 2122407531857015940220601)
            ·
              refine ⟨1591805648892761955165451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2122407531857015940220601 1591805648892761955165451)
              ·
                refine ⟨2387708473339142932748177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1591805648892761955165451 2387708473339142932748177)
                ·
                  refine ⟨1790781355004357199561133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2387708473339142932748177 1790781355004357199561133)
                  ·
                    refine ⟨671543008126633949835425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1790781355004357199561133 671543008126633949835425)
                    ·
                      rfl

theorem cell22_1961738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_1961738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961738 prefixEnd_1961738 := by exact prefixLift 1961738
  have htrace : WordTrace (prefixWord ++ tailWord_1961738) baseStart_1961738 baseEnd_1961738 := by
    simpa [prefixWord, tailWord_1961738, baseEnd_1961738] using wordTrace_append hprefix tailTrace_1961738
  have hstable : (prefixWord ++ tailWord_1961738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961738).length < 2 ^ (prefixWord ++ tailWord_1961738).sum := by decide
  have hdescent : baseEnd_1961738 < baseStart_1961738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961809 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 3, 4]
def baseStart_1961809 : Nat := 118140960795 + 1961809 * 2 ^ 59
def prefixEnd_1961809 : Nat := 4983230072969 + 3 ^ 40 * 1961809 * 2
def baseEnd_1961809 : Nat := 671567312877613431310207

theorem tailTrace_1961809 : CollatzResearch.WordTrace tailWord_1961809 prefixEnd_1961809 671567312877613431310207 := by
  unfold tailWord_1961809
  simp only [CollatzResearch.WordTrace]
  refine ⟨71553052549708518147592481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47702035033139012098394987 71553052549708518147592481)
  ·
    refine ⟨53664789412281388610694361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71553052549708518147592481 53664789412281388610694361)
    ·
      refine ⟨40248592059211041458020771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53664789412281388610694361 40248592059211041458020771)
      ·
        refine ⟨60372888088816562187031157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40248592059211041458020771 60372888088816562187031157)
        ·
          refine ⟨5659958258326552705034171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60372888088816562187031157 5659958258326552705034171)
          ·
            refine ⟨8489937387489829057551257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5659958258326552705034171 8489937387489829057551257)
            ·
              refine ⟨6367453040617371793163443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8489937387489829057551257 6367453040617371793163443)
              ·
                refine ⟨9551179560926057689745165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6367453040617371793163443 9551179560926057689745165)
                ·
                  refine ⟨3581692335347271633654437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9551179560926057689745165 3581692335347271633654437)
                  ·
                    refine ⟨671567312877613431310207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3581692335347271633654437 671567312877613431310207)
                    ·
                      rfl

theorem cell22_1961809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_1961809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961809 prefixEnd_1961809 := by exact prefixLift 1961809
  have htrace : WordTrace (prefixWord ++ tailWord_1961809) baseStart_1961809 baseEnd_1961809 := by
    simpa [prefixWord, tailWord_1961809, baseEnd_1961809] using wordTrace_append hprefix tailTrace_1961809
  have hstable : (prefixWord ++ tailWord_1961809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961809).length < 2 ^ (prefixWord ++ tailWord_1961809).sum := by decide
  have hdescent : baseEnd_1961809 < baseStart_1961809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961867 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 1, 9]
def baseStart_1961867 : Nat := 118140960795 + 1961867 * 2 ^ 59
def prefixEnd_1961867 : Nat := 4983230072969 + 3 ^ 40 * 1961867 * 2
def baseEnd_1961867 : Nat := 671587167462920613360029

theorem tailTrace_1961867 : CollatzResearch.WordTrace tailWord_1961867 prefixEnd_1961867 671587167462920613360029 := by
  unfold tailWord_1961867
  simp only [CollatzResearch.WordTrace]
  refine ⟨71555167983498394053203855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47703445322332262702135903 71555167983498394053203855)
  ·
    refine ⟨107332751975247591079805783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71555167983498394053203855 107332751975247591079805783)
    ·
      refine ⟨160999127962871386619708675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107332751975247591079805783 160999127962871386619708675)
      ·
        refine ⟨241498691944307079929563013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160999127962871386619708675 241498691944307079929563013)
        ·
          refine ⟨45281004739557577486793065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241498691944307079929563013 45281004739557577486793065)
          ·
            refine ⟨33960753554668183115094799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45281004739557577486793065 33960753554668183115094799)
            ·
              refine ⟨50941130332002274672642199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33960753554668183115094799 50941130332002274672642199)
              ·
                refine ⟨76411695498003412008963299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50941130332002274672642199 76411695498003412008963299)
                ·
                  refine ⟨114617543247005118013444949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76411695498003412008963299 114617543247005118013444949)
                  ·
                    refine ⟨671587167462920613360029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 114617543247005118013444949 671587167462920613360029)
                    ·
                      rfl

theorem cell22_1961867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_1961867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961867 prefixEnd_1961867 := by exact prefixLift 1961867
  have htrace : WordTrace (prefixWord ++ tailWord_1961867) baseStart_1961867 baseEnd_1961867 := by
    simpa [prefixWord, tailWord_1961867, baseEnd_1961867] using wordTrace_append hprefix tailTrace_1961867
  have hstable : (prefixWord ++ tailWord_1961867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961867).length < 2 ^ (prefixWord ++ tailWord_1961867).sum := by decide
  have hdescent : baseEnd_1961867 < baseStart_1961867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1961991 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 1, 5]
def baseStart_1961991 : Nat := 118140960795 + 1961991 * 2 ^ 59
def prefixEnd_1961991 : Nat := 4983230072969 + 3 ^ 40 * 1961991 * 2
def baseEnd_1961991 : Nat := 671629615197025623259649

theorem tailTrace_1961991 : CollatzResearch.WordTrace tailWord_1961991 prefixEnd_1961991 671629615197025623259649 := by
  unfold tailWord_1961991
  simp only [CollatzResearch.WordTrace]
  refine ⟨71559690635049163230717827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47706460423366108820478551 71559690635049163230717827)
  ·
    refine ⟨107339535952573744846076741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71559690635049163230717827 107339535952573744846076741)
    ·
      refine ⟨20126162991107577158639389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107339535952573744846076741 20126162991107577158639389)
      ·
        refine ⟨7547311121665341434489771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20126162991107577158639389 7547311121665341434489771)
        ·
          refine ⟨11320966682498012151734657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7547311121665341434489771 11320966682498012151734657)
          ·
            refine ⟨8490725011873509113800993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11320966682498012151734657 8490725011873509113800993)
            ·
              refine ⟨6368043758905131835350745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8490725011873509113800993 6368043758905131835350745)
              ·
                refine ⟨4776032819178848876513059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6368043758905131835350745 4776032819178848876513059)
                ·
                  refine ⟨7164049228768273314769589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776032819178848876513059 7164049228768273314769589)
                  ·
                    refine ⟨671629615197025623259649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7164049228768273314769589 671629615197025623259649)
                    ·
                      rfl

theorem cell22_1961991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_1961991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1961991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1961991 prefixEnd_1961991 := by exact prefixLift 1961991
  have htrace : WordTrace (prefixWord ++ tailWord_1961991) baseStart_1961991 baseEnd_1961991 := by
    simpa [prefixWord, tailWord_1961991, baseEnd_1961991] using wordTrace_append hprefix tailTrace_1961991
  have hstable : (prefixWord ++ tailWord_1961991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1961991).length < 2 ^ (prefixWord ++ tailWord_1961991).sum := by decide
  have hdescent : baseEnd_1961991 < baseStart_1961991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1961991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962083 : List Nat := [1, 1, 1, 5, 1, 1, 6, 1, 5]
def baseStart_1962083 : Nat := 118140960795 + 1962083 * 2 ^ 59
def prefixEnd_1962083 : Nat := 4983230072969 + 3 ^ 40 * 1962083 * 2
def baseEnd_1962083 : Nat := 223887036225722683319789

theorem tailTrace_1962083 : CollatzResearch.WordTrace tailWord_1962083 prefixEnd_1962083 223887036225722683319789 := by
  unfold tailWord_1962083
  simp only [CollatzResearch.WordTrace]
  refine ⟨71563046150715862943066903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47708697433810575295377935 71563046150715862943066903)
  ·
    refine ⟨107344569226073794414600355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71563046150715862943066903 107344569226073794414600355)
    ·
      refine ⟨161016853839110691621900533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107344569226073794414600355 161016853839110691621900533)
      ·
        refine ⟨15095330047416627339553175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 161016853839110691621900533 15095330047416627339553175)
        ·
          refine ⟨22642995071124941009329763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15095330047416627339553175 22642995071124941009329763)
          ·
            refine ⟨33964492606687411513994645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22642995071124941009329763 33964492606687411513994645)
            ·
              refine ⟨1592085590938472414718499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33964492606687411513994645 1592085590938472414718499)
              ·
                refine ⟨2388128386407708622077749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592085590938472414718499 2388128386407708622077749)
                ·
                  refine ⟨223887036225722683319789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2388128386407708622077749 223887036225722683319789)
                  ·
                    rfl

theorem cell22_1962083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 5].length) (baseStart_1962083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962083 prefixEnd_1962083 := by exact prefixLift 1962083
  have htrace : WordTrace (prefixWord ++ tailWord_1962083) baseStart_1962083 baseEnd_1962083 := by
    simpa [prefixWord, tailWord_1962083, baseEnd_1962083] using wordTrace_append hprefix tailTrace_1962083
  have hstable : (prefixWord ++ tailWord_1962083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962083).length < 2 ^ (prefixWord ++ tailWord_1962083).sum := by decide
  have hdescent : baseEnd_1962083 < baseStart_1962083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962128 : List Nat := [2, 1, 1, 1, 1, 1, 7, 4, 4]
def baseStart_1962128 : Nat := 118140960795 + 1962128 * 2 ^ 59
def prefixEnd_1962128 : Nat := 4983230072969 + 3 ^ 40 * 1962128 * 2
def baseEnd_1962128 : Nat := 223892171032267644194743

theorem tailTrace_1962128 : CollatzResearch.WordTrace tailWord_1962128 prefixEnd_1962128 223892171032267644194743 := by
  unfold tailWord_1962128
  simp only [CollatzResearch.WordTrace]
  refine ⟨35782343717776417814227519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47709791623701890418970025 35782343717776417814227519)
  ·
    refine ⟨53673515576664626721341279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35782343717776417814227519 53673515576664626721341279)
    ·
      refine ⟨80510273364996940082011919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53673515576664626721341279 80510273364996940082011919)
      ·
        refine ⟨120765410047495410123017879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80510273364996940082011919 120765410047495410123017879)
        ·
          refine ⟨181148115071243115184526819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120765410047495410123017879 181148115071243115184526819)
          ·
            refine ⟨271722172606864672776790229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181148115071243115184526819 271722172606864672776790229)
            ·
              refine ⟨6368488420473390768206021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 271722172606864672776790229 6368488420473390768206021)
              ·
                refine ⟨1194091578838760769038629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6368488420473390768206021 1194091578838760769038629)
                ·
                  refine ⟨223892171032267644194743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1194091578838760769038629 223892171032267644194743)
                  ·
                    rfl

theorem cell22_1962128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 4].length) (baseStart_1962128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962128 prefixEnd_1962128 := by exact prefixLift 1962128
  have htrace : WordTrace (prefixWord ++ tailWord_1962128) baseStart_1962128 baseEnd_1962128 := by
    simpa [prefixWord, tailWord_1962128, baseEnd_1962128] using wordTrace_append hprefix tailTrace_1962128
  have hstable : (prefixWord ++ tailWord_1962128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962128).length < 2 ^ (prefixWord ++ tailWord_1962128).sum := by decide
  have hdescent : baseEnd_1962128 < baseStart_1962128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962143 : List Nat := [1, 1, 2, 6, 1, 1, 1, 3, 1, 5]
def baseStart_1962143 : Nat := 118140960795 + 1962143 * 2 ^ 59
def prefixEnd_1962143 : Nat := 4983230072969 + 3 ^ 40 * 1962143 * 2
def baseEnd_1962143 : Nat := 671681647903347893459183

theorem tailTrace_1962143 : CollatzResearch.WordTrace tailWord_1962143 prefixEnd_1962143 671681647903347893459183 := by
  unfold tailWord_1962143
  simp only [CollatzResearch.WordTrace]
  refine ⟨71565234530498493190251083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47710156353665662126834055 71565234530498493190251083)
  ·
    refine ⟨107347851795747739785376625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71565234530498493190251083 107347851795747739785376625)
    ·
      refine ⟨80510888846810804839032469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107347851795747739785376625 80510888846810804839032469)
      ·
        refine ⟨3773947914694256476829647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80510888846810804839032469 3773947914694256476829647)
        ·
          refine ⟨5660921872041384715244471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3773947914694256476829647 5660921872041384715244471)
          ·
            refine ⟨8491382808062077072866707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5660921872041384715244471 8491382808062077072866707)
            ·
              refine ⟨12737074212093115609300061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8491382808062077072866707 12737074212093115609300061)
              ·
                refine ⟨4776402829534918353487523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12737074212093115609300061 4776402829534918353487523)
                ·
                  refine ⟨7164604244302377530231285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4776402829534918353487523 7164604244302377530231285)
                  ·
                    refine ⟨671681647903347893459183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7164604244302377530231285 671681647903347893459183)
                    ·
                      rfl

theorem cell22_1962143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_1962143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962143 prefixEnd_1962143 := by exact prefixLift 1962143
  have htrace : WordTrace (prefixWord ++ tailWord_1962143) baseStart_1962143 baseEnd_1962143 := by
    simpa [prefixWord, tailWord_1962143, baseEnd_1962143] using wordTrace_append hprefix tailTrace_1962143
  have hstable : (prefixWord ++ tailWord_1962143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962143).length < 2 ^ (prefixWord ++ tailWord_1962143).sum := by decide
  have hdescent : baseEnd_1962143 < baseStart_1962143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962177 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1962177 : Nat := 118140960795 + 1962177 * 2 ^ 59
def prefixEnd_1962177 : Nat := 4983230072969 + 3 ^ 40 * 1962177 * 2
def baseEnd_1962177 : Nat := 671693286798183138109079

theorem tailTrace_1962177 : CollatzResearch.WordTrace tailWord_1962177 prefixEnd_1962177 671693286798183138109079 := by
  unfold tailWord_1962177
  simp only [CollatzResearch.WordTrace]
  refine ⟨71566474612375316996988785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47710983074916877997992523 71566474612375316996988785)
  ·
    refine ⟨53674855959281487747741589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71566474612375316996988785 53674855959281487747741589)
    ·
      refine ⟨2516008873091319738175387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53674855959281487747741589 2516008873091319738175387)
      ·
        refine ⟨3774013309636979607263081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2516008873091319738175387 3774013309636979607263081)
        ·
          refine ⟨2830509982227734705447311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3774013309636979607263081 2830509982227734705447311)
          ·
            refine ⟨4245764973341602058170967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2830509982227734705447311 4245764973341602058170967)
            ·
              refine ⟨6368647460012403087256451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4245764973341602058170967 6368647460012403087256451)
              ·
                refine ⟨9552971190018604630884677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6368647460012403087256451 9552971190018604630884677)
                ·
                  refine ⟨1791182098128488368290877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9552971190018604630884677 1791182098128488368290877)
                  ·
                    refine ⟨671693286798183138109079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1791182098128488368290877 671693286798183138109079)
                    ·
                      rfl

theorem cell22_1962177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1962177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962177 prefixEnd_1962177 := by exact prefixLift 1962177
  have htrace : WordTrace (prefixWord ++ tailWord_1962177) baseStart_1962177 baseEnd_1962177 := by
    simpa [prefixWord, tailWord_1962177, baseEnd_1962177] using wordTrace_append hprefix tailTrace_1962177
  have hstable : (prefixWord ++ tailWord_1962177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962177).length < 2 ^ (prefixWord ++ tailWord_1962177).sum := by decide
  have hdescent : baseEnd_1962177 < baseStart_1962177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962297 : List Nat := [1, 2, 1, 6, 1, 2, 1, 4, 4]
def baseStart_1962297 : Nat := 118140960795 + 1962297 * 2 ^ 59
def prefixEnd_1962297 : Nat := 4983230072969 + 3 ^ 40 * 1962297 * 2
def baseEnd_1962297 : Nat := 223911455083514275036237

theorem tailTrace_1962297 : CollatzResearch.WordTrace tailWord_1962297 prefixEnd_1962297 223911455083514275036237 := by
  unfold tailWord_1962297
  simp only [CollatzResearch.WordTrace]
  refine ⟨71570851371940577491357145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47713900914627051660904763 71570851371940577491357145)
  ·
    refine ⟨53678138528955433118517859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71570851371940577491357145 53678138528955433118517859)
    ·
      refine ⟨80517207793433149677776789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53678138528955433118517859 80517207793433149677776789)
      ·
        refine ⟨3774244115317178891145787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80517207793433149677776789 3774244115317178891145787)
        ·
          refine ⟨5661366172975768336718681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3774244115317178891145787 5661366172975768336718681)
          ·
            refine ⟨4246024629731826252539011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5661366172975768336718681 4246024629731826252539011)
            ·
              refine ⟨6369036944597739378808517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4246024629731826252539011 6369036944597739378808517)
              ·
                refine ⟨1194194427112076133526597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6369036944597739378808517 1194194427112076133526597)
                ·
                  refine ⟨223911455083514275036237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1194194427112076133526597 223911455083514275036237)
                  ·
                    rfl

theorem cell22_1962297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 4].length) (baseStart_1962297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962297 prefixEnd_1962297 := by exact prefixLift 1962297
  have htrace : WordTrace (prefixWord ++ tailWord_1962297) baseStart_1962297 baseEnd_1962297 := by
    simpa [prefixWord, tailWord_1962297, baseEnd_1962297] using wordTrace_append hprefix tailTrace_1962297
  have hstable : (prefixWord ++ tailWord_1962297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962297).length < 2 ^ (prefixWord ++ tailWord_1962297).sum := by decide
  have hdescent : baseEnd_1962297 < baseStart_1962297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962340 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_1962340 : Nat := 118140960795 + 1962340 * 2 ^ 59
def prefixEnd_1962340 : Nat := 4983230072969 + 3 ^ 40 * 1962340 * 2
def baseEnd_1962340 : Nat := 671749085029305046283579

theorem tailTrace_1962340 : CollatzResearch.WordTrace tailWord_1962340 prefixEnd_1962340 671749085029305046283579 := by
  unfold tailWord_1962340
  simp only [CollatzResearch.WordTrace]
  refine ⟨35786209855392397917586237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47714946473856530556781649 35786209855392397917586237)
  ·
    refine ⟨13419828695772149219094839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35786209855392397917586237 13419828695772149219094839)
    ·
      refine ⟨20129743043658223828642259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13419828695772149219094839 20129743043658223828642259)
      ·
        refine ⟨30194614565487335742963389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20129743043658223828642259 30194614565487335742963389)
        ·
          refine ⟨11322980462057750903611271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30194614565487335742963389 11322980462057750903611271)
          ·
            refine ⟨16984470693086626355416907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11322980462057750903611271 16984470693086626355416907)
            ·
              refine ⟨25476706039629939533125361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16984470693086626355416907 25476706039629939533125361)
              ·
                refine ⟨19107529529722454649844021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25476706039629939533125361 19107529529722454649844021)
                ·
                  refine ⟨1791330893411480123422877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19107529529722454649844021 1791330893411480123422877)
                  ·
                    refine ⟨671749085029305046283579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1791330893411480123422877 671749085029305046283579)
                    ·
                      rfl

theorem cell22_1962340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_1962340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962340 prefixEnd_1962340 := by exact prefixLift 1962340
  have htrace : WordTrace (prefixWord ++ tailWord_1962340) baseStart_1962340 baseEnd_1962340 := by
    simpa [prefixWord, tailWord_1962340, baseEnd_1962340] using wordTrace_append hprefix tailTrace_1962340
  have hstable : (prefixWord ++ tailWord_1962340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962340).length < 2 ^ (prefixWord ++ tailWord_1962340).sum := by decide
  have hdescent : baseEnd_1962340 < baseStart_1962340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962357 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1962357 : Nat := 118140960795 + 1962357 * 2 ^ 59
def prefixEnd_1962357 : Nat := 4983230072969 + 3 ^ 40 * 1962357 * 2
def baseEnd_1962357 : Nat := 671754904476722668608527

theorem tailTrace_1962357 : CollatzResearch.WordTrace tailWord_1962357 prefixEnd_1962357 671754904476722668608527 := by
  unfold tailWord_1962357
  simp only [CollatzResearch.WordTrace]
  refine ⟨71573039751723207738541325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47715359834482138492360883 71573039751723207738541325)
  ·
    refine ⟨26839889906896202901952997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71573039751723207738541325 26839889906896202901952997)
    ·
      refine ⟨5032479357543038044116187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26839889906896202901952997 5032479357543038044116187)
      ·
        refine ⟨7548719036314557066174281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5032479357543038044116187 7548719036314557066174281)
        ·
          refine ⟨5661539277235917799630711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7548719036314557066174281 5661539277235917799630711)
          ·
            refine ⟨8492308915853876699446067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5661539277235917799630711 8492308915853876699446067)
            ·
              refine ⟨12738463373780815049169101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8492308915853876699446067 12738463373780815049169101)
              ·
                refine ⟨4776923765167805643438413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12738463373780815049169101 4776923765167805643438413)
                ·
                  refine ⟨1791346411937927116289405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4776923765167805643438413 1791346411937927116289405)
                  ·
                    refine ⟨671754904476722668608527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1791346411937927116289405 671754904476722668608527)
                    ·
                      rfl

theorem cell22_1962357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1962357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962357 prefixEnd_1962357 := by exact prefixLift 1962357
  have htrace : WordTrace (prefixWord ++ tailWord_1962357) baseStart_1962357 baseEnd_1962357 := by
    simpa [prefixWord, tailWord_1962357, baseEnd_1962357] using wordTrace_append hprefix tailTrace_1962357
  have hstable : (prefixWord ++ tailWord_1962357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962357).length < 2 ^ (prefixWord ++ tailWord_1962357).sum := by decide
  have hdescent : baseEnd_1962357 < baseStart_1962357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962408 : List Nat := [2, 1, 6, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1962408 : Nat := 118140960795 + 1962408 * 2 ^ 59
def prefixEnd_1962408 : Nat := 4983230072969 + 3 ^ 40 * 1962408 * 2
def baseEnd_1962408 : Nat := 671772362818975535583371

theorem tailTrace_1962408 : CollatzResearch.WordTrace tailWord_1962408 prefixEnd_1962408 671772362818975535583371 := by
  unfold tailWord_1962408
  simp only [CollatzResearch.WordTrace]
  refine ⟨35787449937269221724323939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47716599916358962299098585 35787449937269221724323939)
  ·
    refine ⟨53681174905903832586485909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35787449937269221724323939 53681174905903832586485909)
    ·
      refine ⟨2516305073714242152491527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53681174905903832586485909 2516305073714242152491527)
      ·
        refine ⟨3774457610571363228737291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2516305073714242152491527 3774457610571363228737291)
        ·
          refine ⟨5661686415857044843105937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3774457610571363228737291 5661686415857044843105937)
          ·
            refine ⟨4246264811892783632329453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5661686415857044843105937 4246264811892783632329453)
            ·
              refine ⟨1592349304459793862123545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4246264811892783632329453 1592349304459793862123545)
              ·
                refine ⟨1194261978344845396592659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1592349304459793862123545 1194261978344845396592659)
                ·
                  refine ⟨1791392967517268094888989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194261978344845396592659 1791392967517268094888989)
                  ·
                    refine ⟨671772362818975535583371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1791392967517268094888989 671772362818975535583371)
                    ·
                      rfl

theorem cell22_1962408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1962408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962408 prefixEnd_1962408 := by exact prefixLift 1962408
  have htrace : WordTrace (prefixWord ++ tailWord_1962408) baseStart_1962408 baseEnd_1962408 := by
    simpa [prefixWord, tailWord_1962408, baseEnd_1962408] using wordTrace_append hprefix tailTrace_1962408
  have hstable : (prefixWord ++ tailWord_1962408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962408).length < 2 ^ (prefixWord ++ tailWord_1962408).sum := by decide
  have hdescent : baseEnd_1962408 < baseStart_1962408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962421 : List Nat := [1, 3, 3, 2, 4, 1, 2, 1, 5]
def baseStart_1962421 : Nat := 118140960795 + 1962421 * 2 ^ 59
def prefixEnd_1962421 : Nat := 4983230072969 + 3 ^ 40 * 1962421 * 2
def baseEnd_1962421 : Nat := 223925604328215945002777

theorem tailTrace_1962421 : CollatzResearch.WordTrace tailWord_1962421 prefixEnd_1962421 223925604328215945002777 := by
  unfold tailWord_1962421
  simp only [CollatzResearch.WordTrace]
  refine ⟨71575374023491346668871117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47716916015660897779247411 71575374023491346668871117)
  ·
    refine ⟨26840765258809255000826669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71575374023491346668871117 26840765258809255000826669)
    ·
      refine ⟨10065286972053470625310001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26840765258809255000826669 10065286972053470625310001)
      ·
        refine ⟨7548965229040102968982501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10065286972053470625310001 7548965229040102968982501)
        ·
          refine ⟨1415430980445019306684219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7548965229040102968982501 1415430980445019306684219)
          ·
            refine ⟨2123146470667528960026329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1415430980445019306684219 2123146470667528960026329)
            ·
              refine ⟨1592359853000646720019747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2123146470667528960026329 1592359853000646720019747)
              ·
                refine ⟨2388539779500970080029621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592359853000646720019747 2388539779500970080029621)
                ·
                  refine ⟨223925604328215945002777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2388539779500970080029621 223925604328215945002777)
                  ·
                    rfl

theorem cell22_1962421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_1962421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962421 prefixEnd_1962421 := by exact prefixLift 1962421
  have htrace : WordTrace (prefixWord ++ tailWord_1962421) baseStart_1962421 baseEnd_1962421 := by
    simpa [prefixWord, tailWord_1962421, baseEnd_1962421] using wordTrace_append hprefix tailTrace_1962421
  have hstable : (prefixWord ++ tailWord_1962421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962421).length < 2 ^ (prefixWord ++ tailWord_1962421).sum := by decide
  have hdescent : baseEnd_1962421 < baseStart_1962421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962477 : List Nat := [1, 5, 1, 3, 1, 1, 3, 7]
def baseStart_1962477 : Nat := 118140960795 + 1962477 * 2 ^ 59
def prefixEnd_1962477 : Nat := 4983230072969 + 3 ^ 40 * 1962477 * 2
def baseEnd_1962477 : Nat := 74643998103231372845351

theorem tailTrace_1962477 : CollatzResearch.WordTrace tailWord_1962477 prefixEnd_1962477 74643998103231372845351 := by
  unfold tailWord_1962477
  simp only [CollatzResearch.WordTrace]
  refine ⟨71577416511288468232909685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47718277674192312155273123 71577416511288468232909685)
  ·
    refine ⟨6710382797933293896835283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71577416511288468232909685 6710382797933293896835283)
    ·
      refine ⟨10065574196899940845252925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6710382797933293896835283 10065574196899940845252925)
      ·
        refine ⟨3774590323837477816969847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10065574196899940845252925 3774590323837477816969847)
        ·
          refine ⟨5661885485756216725454771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3774590323837477816969847 5661885485756216725454771)
          ·
            refine ⟨8492828228634325088182157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5661885485756216725454771 8492828228634325088182157)
            ·
              refine ⟨3184810585737871908068309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8492828228634325088182157 3184810585737871908068309)
              ·
                refine ⟨74643998103231372845351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3184810585737871908068309 74643998103231372845351)
                ·
                  rfl

theorem cell22_1962477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 3, 7].length) (baseStart_1962477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962477 prefixEnd_1962477 := by exact prefixLift 1962477
  have htrace : WordTrace (prefixWord ++ tailWord_1962477) baseStart_1962477 baseEnd_1962477 := by
    simpa [prefixWord, tailWord_1962477, baseEnd_1962477] using wordTrace_append hprefix tailTrace_1962477
  have hstable : (prefixWord ++ tailWord_1962477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962477).length < 2 ^ (prefixWord ++ tailWord_1962477).sum := by decide
  have hdescent : baseEnd_1962477 < baseStart_1962477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962522 : List Nat := [3, 1, 1, 3, 1, 1, 5, 2, 5]
def baseStart_1962522 : Nat := 118140960795 + 1962522 * 2 ^ 59
def prefixEnd_1962522 : Nat := 4983230072969 + 3 ^ 40 * 1962522 * 2
def baseEnd_1962522 : Nat := 223937129116239079411007

theorem tailTrace_1962522 : CollatzResearch.WordTrace tailWord_1962522 prefixEnd_1962522 223937129116239079411007 := by
  unfold tailWord_1962522
  simp only [CollatzResearch.WordTrace]
  refine ⟨17894764449031360229574455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47719371864083627278865213 17894764449031360229574455)
  ·
    refine ⟨26842146673547040344361683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17894764449031360229574455 26842146673547040344361683)
    ·
      refine ⟨40263220010320560516542525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26842146673547040344361683 40263220010320560516542525)
      ·
        refine ⟨15098707503870210193703447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40263220010320560516542525 15098707503870210193703447)
        ·
          refine ⟨22648061255805315290555171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15098707503870210193703447 22648061255805315290555171)
          ·
            refine ⟨33972091883707972935832757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22648061255805315290555171 33972091883707972935832757)
            ·
              refine ⟨3184883614097622462734321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33972091883707972935832757 3184883614097622462734321)
              ·
                refine ⟨2388662710573216847050741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3184883614097622462734321 2388662710573216847050741)
                ·
                  refine ⟨223937129116239079411007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2388662710573216847050741 223937129116239079411007)
                  ·
                    rfl

theorem cell22_1962522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_1962522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962522 prefixEnd_1962522 := by exact prefixLift 1962522
  have htrace : WordTrace (prefixWord ++ tailWord_1962522) baseStart_1962522 baseEnd_1962522 := by
    simpa [prefixWord, tailWord_1962522, baseEnd_1962522] using wordTrace_append hprefix tailTrace_1962522
  have hstable : (prefixWord ++ tailWord_1962522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962522).length < 2 ^ (prefixWord ++ tailWord_1962522).sum := by decide
  have hdescent : baseEnd_1962522 < baseStart_1962522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962708 : List Nat := [2, 4, 1, 3, 2, 1, 3, 1, 5]
def baseStart_1962708 : Nat := 118140960795 + 1962708 * 2 ^ 59
def prefixEnd_1962708 : Nat := 4983230072969 + 3 ^ 40 * 1962708 * 2
def baseEnd_1962708 : Nat := 223958352983291584360817

theorem tailTrace_1962708 : CollatzResearch.WordTrace tailWord_1962708 prefixEnd_1962708 223958352983291584360817 := by
  unfold tailWord_1962708
  simp only [CollatzResearch.WordTrace]
  refine ⟨35792920886725797342284389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47723894515634396456379185 35792920886725797342284389)
  ·
    refine ⟨6711172666261087001678323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35792920886725797342284389 6711172666261087001678323)
    ·
      refine ⟨10066758999391630502517485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6711172666261087001678323 10066758999391630502517485)
      ·
        refine ⟨3775034624771861438444057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10066758999391630502517485 3775034624771861438444057)
        ·
          refine ⟨2831275968578896078833043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3775034624771861438444057 2831275968578896078833043)
          ·
            refine ⟨4246913952868344118249565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831275968578896078833043 4246913952868344118249565)
            ·
              refine ⟨1592592732325629044343587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4246913952868344118249565 1592592732325629044343587)
              ·
                refine ⟨2388889098488443566515381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1592592732325629044343587 2388889098488443566515381)
                ·
                  refine ⟨223958352983291584360817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2388889098488443566515381 223958352983291584360817)
                  ·
                    rfl

theorem cell22_1962708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_1962708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962708 prefixEnd_1962708 := by exact prefixLift 1962708
  have htrace : WordTrace (prefixWord ++ tailWord_1962708) baseStart_1962708 baseEnd_1962708 := by
    simpa [prefixWord, tailWord_1962708, baseEnd_1962708] using wordTrace_append hprefix tailTrace_1962708
  have hstable : (prefixWord ++ tailWord_1962708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962708).length < 2 ^ (prefixWord ++ tailWord_1962708).sum := by decide
  have hdescent : baseEnd_1962708 < baseStart_1962708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962721 : List Nat := [1, 2, 3, 1, 4, 2, 2, 2, 1, 4]
def baseStart_1962721 : Nat := 118140960795 + 1962721 * 2 ^ 59
def prefixEnd_1962721 : Nat := 4983230072969 + 3 ^ 40 * 1962721 * 2
def baseEnd_1962721 : Nat := 671879509115547052507411

theorem tailTrace_1962721 : CollatzResearch.WordTrace tailWord_1962721 prefixEnd_1962721 671879509115547052507411 := by
  unfold tailWord_1962721
  simp only [CollatzResearch.WordTrace]
  refine ⟨71586315922404497904792017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47724210614936331936528011 71586315922404497904792017)
  ·
    refine ⟨53689736941803373428594013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71586315922404497904792017 53689736941803373428594013)
    ·
      refine ⟨20133651353176265035722755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53689736941803373428594013 20133651353176265035722755)
      ·
        refine ⟨30200477029764397553584133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20133651353176265035722755 30200477029764397553584133)
        ·
          refine ⟨5662589443080824541297025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30200477029764397553584133 5662589443080824541297025)
          ·
            refine ⟨4246942082310618405972769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5662589443080824541297025 4246942082310618405972769)
            ·
              refine ⟨3185206561732963804479577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4246942082310618405972769 3185206561732963804479577)
              ·
                refine ⟨2388904921299722853359683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3185206561732963804479577 2388904921299722853359683)
                ·
                  refine ⟨3583357381949584280039525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2388904921299722853359683 3583357381949584280039525)
                  ·
                    refine ⟨671879509115547052507411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3583357381949584280039525 671879509115547052507411)
                    ·
                      rfl

theorem cell22_1962721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_1962721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962721 prefixEnd_1962721 := by exact prefixLift 1962721
  have htrace : WordTrace (prefixWord ++ tailWord_1962721) baseStart_1962721 baseEnd_1962721 := by
    simpa [prefixWord, tailWord_1962721, baseEnd_1962721] using wordTrace_append hprefix tailTrace_1962721
  have hstable : (prefixWord ++ tailWord_1962721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962721).length < 2 ^ (prefixWord ++ tailWord_1962721).sum := by decide
  have hdescent : baseEnd_1962721 < baseStart_1962721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962749 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_1962749 : Nat := 118140960795 + 1962749 * 2 ^ 59
def prefixEnd_1962749 : Nat := 4983230072969 + 3 ^ 40 * 1962749 * 2
def baseEnd_1962749 : Nat := 671889094087764312807325

theorem tailTrace_1962749 : CollatzResearch.WordTrace tailWord_1962749 prefixEnd_1962749 671889094087764312807325 := by
  unfold tailWord_1962749
  simp only [CollatzResearch.WordTrace]
  refine ⟨71587337166303058686811301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47724891444202039124540867 71587337166303058686811301)
  ·
    refine ⟨13422625718681823503777119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71587337166303058686811301 13422625718681823503777119)
    ·
      refine ⟨20133938578022735255665679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13422625718681823503777119 20133938578022735255665679)
      ·
        refine ⟨30200907867034102883498519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20133938578022735255665679 30200907867034102883498519)
        ·
          refine ⟨45301361800551154325247779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30200907867034102883498519 45301361800551154325247779)
          ·
            refine ⟨67952042700826731487871669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45301361800551154325247779 67952042700826731487871669)
            ·
              refine ⟨6370504003202506076987969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67952042700826731487871669 6370504003202506076987969)
              ·
                refine ⟨4777878002401879557740977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6370504003202506076987969 4777878002401879557740977)
                ·
                  refine ⟨3583408501801409668305733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4777878002401879557740977 3583408501801409668305733)
                  ·
                    refine ⟨671889094087764312807325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3583408501801409668305733 671889094087764312807325)
                    ·
                      rfl

theorem cell22_1962749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_1962749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962749 prefixEnd_1962749 := by exact prefixLift 1962749
  have htrace : WordTrace (prefixWord ++ tailWord_1962749) baseStart_1962749 baseEnd_1962749 := by
    simpa [prefixWord, tailWord_1962749, baseEnd_1962749] using wordTrace_append hprefix tailTrace_1962749
  have hstable : (prefixWord ++ tailWord_1962749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962749).length < 2 ^ (prefixWord ++ tailWord_1962749).sum := by decide
  have hdescent : baseEnd_1962749 < baseStart_1962749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962777 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 4, 6]
def baseStart_1962777 : Nat := 118140960795 + 1962777 * 2 ^ 59
def prefixEnd_1962777 : Nat := 4983230072969 + 3 ^ 40 * 1962777 * 2
def baseEnd_1962777 : Nat := 671898679059981573107239

theorem tailTrace_1962777 : CollatzResearch.WordTrace tailWord_1962777 prefixEnd_1962777 671898679059981573107239 := by
  unfold tailWord_1962777
  simp only [CollatzResearch.WordTrace]
  refine ⟨71588358410201619468830585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47725572273467746312553723 71588358410201619468830585)
  ·
    refine ⟨53691268807651214601622939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71588358410201619468830585 53691268807651214601622939)
    ·
      refine ⟨80536903211476821902434409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53691268807651214601622939 80536903211476821902434409)
      ·
        refine ⟨60402677408607616426825807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80536903211476821902434409 60402677408607616426825807)
        ·
          refine ⟨90604016112911424640238711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60402677408607616426825807 90604016112911424640238711)
          ·
            refine ⟨135906024169367136960358067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90604016112911424640238711 135906024169367136960358067)
            ·
              refine ⟨203859036254050705440537101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135906024169367136960358067 203859036254050705440537101)
              ·
                refine ⟨76447138595269014540201413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203859036254050705440537101 76447138595269014540201413)
                ·
                  refine ⟨14333838486612940226287765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76447138595269014540201413 14333838486612940226287765)
                  ·
                    refine ⟨671898679059981573107239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14333838486612940226287765 671898679059981573107239)
                    ·
                      rfl

theorem cell22_1962777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_1962777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962777 prefixEnd_1962777 := by exact prefixLift 1962777
  have htrace : WordTrace (prefixWord ++ tailWord_1962777) baseStart_1962777 baseEnd_1962777 := by
    simpa [prefixWord, tailWord_1962777, baseEnd_1962777] using wordTrace_append hprefix tailTrace_1962777
  have hstable : (prefixWord ++ tailWord_1962777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962777).length < 2 ^ (prefixWord ++ tailWord_1962777).sum := by decide
  have hdescent : baseEnd_1962777 < baseStart_1962777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962824 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 2, 5]
def baseStart_1962824 : Nat := 118140960795 + 1962824 * 2 ^ 59
def prefixEnd_1962824 : Nat := 4983230072969 + 3 ^ 40 * 1962824 * 2
def baseEnd_1962824 : Nat := 671914768120489117182095

theorem tailTrace_1962824 : CollatzResearch.WordTrace tailWord_1962824 prefixEnd_1962824 671914768120489117182095 := by
  unfold tailWord_1962824
  simp only [CollatzResearch.WordTrace]
  refine ⟨35795036320515673247895763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47726715094020897663861017 35795036320515673247895763)
  ·
    refine ⟨53692554480773509871843645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35795036320515673247895763 53692554480773509871843645)
    ·
      refine ⟨20134707930290066201941367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53692554480773509871843645 20134707930290066201941367)
      ·
        refine ⟨30202061895435099302912051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20134707930290066201941367 30202061895435099302912051)
        ·
          refine ⟨45303092843152648954368077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30202061895435099302912051 45303092843152648954368077)
          ·
            refine ⟨16988659816182243357888029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45303092843152648954368077 16988659816182243357888029)
            ·
              refine ⟨6370747431068341259208011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16988659816182243357888029 6370747431068341259208011)
              ·
                refine ⟨9556121146602511888812017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6370747431068341259208011 9556121146602511888812017)
                ·
                  refine ⟨7167090859951883916609013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9556121146602511888812017 7167090859951883916609013)
                  ·
                    refine ⟨671914768120489117182095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7167090859951883916609013 671914768120489117182095)
                    ·
                      rfl

theorem cell22_1962824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_1962824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962824 prefixEnd_1962824 := by exact prefixLift 1962824
  have htrace : WordTrace (prefixWord ++ tailWord_1962824) baseStart_1962824 baseEnd_1962824 := by
    simpa [prefixWord, tailWord_1962824, baseEnd_1962824] using wordTrace_append hprefix tailTrace_1962824
  have hstable : (prefixWord ++ tailWord_1962824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962824).length < 2 ^ (prefixWord ++ tailWord_1962824).sum := by decide
  have hdescent : baseEnd_1962824 < baseStart_1962824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962931 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 3, 3]
def baseStart_1962931 : Nat := 118140960795 + 1962931 * 2 ^ 59
def prefixEnd_1962931 : Nat := 4983230072969 + 3 ^ 40 * 1962931 * 2
def baseEnd_1962931 : Nat := 671951396407176504756767

theorem tailTrace_1962931 : CollatzResearch.WordTrace tailWord_1962931 prefixEnd_1962931 671951396407176504756767 := by
  unfold tailWord_1962931
  simp only [CollatzResearch.WordTrace]
  refine ⟨71593975251643703769936647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47729316834429135846624431 71593975251643703769936647)
  ·
    refine ⟨107390962877465555654904971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71593975251643703769936647 107390962877465555654904971)
    ·
      refine ⟨161086444316198333482357457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107390962877465555654904971 161086444316198333482357457)
      ·
        refine ⟨120814833237148750111768093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161086444316198333482357457 120814833237148750111768093)
        ·
          refine ⟨45305562463930781291913035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120814833237148750111768093 45305562463930781291913035)
          ·
            refine ⟨67958343695896171937869553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45305562463930781291913035 67958343695896171937869553)
            ·
              refine ⟨50968757771922128953402165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67958343695896171937869553 50968757771922128953402165)
              ·
                refine ⟨4778321041117699589381453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50968757771922128953402165 4778321041117699589381453)
                ·
                  refine ⟨1791870390419137346018045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4778321041117699589381453 1791870390419137346018045)
                  ·
                    refine ⟨671951396407176504756767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1791870390419137346018045 671951396407176504756767)
                    ·
                      rfl

theorem cell22_1962931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 3].length) (baseStart_1962931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962931 prefixEnd_1962931 := by exact prefixLift 1962931
  have htrace : WordTrace (prefixWord ++ tailWord_1962931) baseStart_1962931 baseEnd_1962931 := by
    simpa [prefixWord, tailWord_1962931, baseEnd_1962931] using wordTrace_append hprefix tailTrace_1962931
  have hstable : (prefixWord ++ tailWord_1962931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962931).length < 2 ^ (prefixWord ++ tailWord_1962931).sum := by decide
  have hdescent : baseEnd_1962931 < baseStart_1962931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1962991 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 3, 4]
def baseStart_1962991 : Nat := 118140960795 + 1962991 * 2 ^ 59
def prefixEnd_1962991 : Nat := 4983230072969 + 3 ^ 40 * 1962991 * 2
def baseEnd_1962991 : Nat := 671971935633356348256583

theorem tailTrace_1962991 : CollatzResearch.WordTrace tailWord_1962991 prefixEnd_1962991 671971935633356348256583 := by
  unfold tailWord_1962991
  simp only [CollatzResearch.WordTrace]
  refine ⟨71596163631426334017120827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47730775754284222678080551 71596163631426334017120827)
  ·
    refine ⟨107394245447139501025681241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71596163631426334017120827 107394245447139501025681241)
    ·
      refine ⟨80545684085354625769260931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107394245447139501025681241 80545684085354625769260931)
      ·
        refine ⟨120818526128031938653891397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80545684085354625769260931 120818526128031938653891397)
        ·
          refine ⟨22653473649005988497604637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120818526128031938653891397 22653473649005988497604637)
          ·
            refine ⟨8495052618377245686601739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22653473649005988497604637 8495052618377245686601739)
            ·
              refine ⟨12742578927565868529902609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8495052618377245686601739 12742578927565868529902609)
              ·
                refine ⟨9556934195674401397426957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12742578927565868529902609 9556934195674401397426957)
                ·
                  refine ⟨3583850323377900524035109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9556934195674401397426957 3583850323377900524035109)
                  ·
                    refine ⟨671971935633356348256583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3583850323377900524035109 671971935633356348256583)
                    ·
                      rfl

theorem cell22_1962991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_1962991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1962991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1962991 prefixEnd_1962991 := by exact prefixLift 1962991
  have htrace : WordTrace (prefixWord ++ tailWord_1962991) baseStart_1962991 baseEnd_1962991 := by
    simpa [prefixWord, tailWord_1962991, baseEnd_1962991] using wordTrace_append hprefix tailTrace_1962991
  have hstable : (prefixWord ++ tailWord_1962991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1962991).length < 2 ^ (prefixWord ++ tailWord_1962991).sum := by decide
  have hdescent : baseEnd_1962991 < baseStart_1962991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1962991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963040 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 6]
def baseStart_1963040 : Nat := 118140960795 + 1963040 * 2 ^ 59
def prefixEnd_1963040 : Nat := 4983230072969 + 3 ^ 40 * 1963040 * 2
def baseEnd_1963040 : Nat := 223996236444912184593811

theorem tailTrace_1963040 : CollatzResearch.WordTrace tailWord_1963040 prefixEnd_1963040 223996236444912184593811 := by
  unfold tailWord_1963040
  simp only [CollatzResearch.WordTrace]
  refine ⟨35798975404124407692827287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47731967205499210257103049 35798975404124407692827287)
  ·
    refine ⟨53698463106186611539240931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35798975404124407692827287 53698463106186611539240931)
    ·
      refine ⟨80547694659279917308861397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53698463106186611539240931 80547694659279917308861397)
      ·
        refine ⟨1887836593576873061926439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 80547694659279917308861397 1887836593576873061926439)
        ·
          refine ⟨2831754890365309592889659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1887836593576873061926439 2831754890365309592889659)
          ·
            refine ⟨4247632335547964389334489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2831754890365309592889659 4247632335547964389334489)
            ·
              refine ⟨3185724251660973292000867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4247632335547964389334489 3185724251660973292000867)
              ·
                refine ⟨4778586377491459938001301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3185724251660973292000867 4778586377491459938001301)
                ·
                  refine ⟨223996236444912184593811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4778586377491459938001301 223996236444912184593811)
                  ·
                    rfl

theorem cell22_1963040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 6].length) (baseStart_1963040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963040 prefixEnd_1963040 := by exact prefixLift 1963040
  have htrace : WordTrace (prefixWord ++ tailWord_1963040) baseStart_1963040 baseEnd_1963040 := by
    simpa [prefixWord, tailWord_1963040, baseEnd_1963040] using wordTrace_append hprefix tailTrace_1963040
  have hstable : (prefixWord ++ tailWord_1963040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963040).length < 2 ^ (prefixWord ++ tailWord_1963040).sum := by decide
  have hdescent : baseEnd_1963040 < baseStart_1963040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963068 : List Nat := [2, 2, 2, 2, 2, 2, 4, 6]
def baseStart_1963068 : Nat := 118140960795 + 1963068 * 2 ^ 59
def prefixEnd_1963068 : Nat := 4983230072969 + 3 ^ 40 * 1963068 * 2
def baseEnd_1963068 : Nat := 74666477145217090453483

theorem tailTrace_1963068 : CollatzResearch.WordTrace tailWord_1963068 prefixEnd_1963068 74666477145217090453483 := by
  unfold tailWord_1963068
  simp only [CollatzResearch.WordTrace]
  refine ⟨35799486026073688083836929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47732648034764917445115905 35799486026073688083836929)
  ·
    refine ⟨26849614519555266062877697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35799486026073688083836929 26849614519555266062877697)
    ·
      refine ⟨20137210889666449547158273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26849614519555266062877697 20137210889666449547158273)
      ·
        refine ⟨15102908167249837160368705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20137210889666449547158273 15102908167249837160368705)
        ·
          refine ⟨11327181125437377870276529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15102908167249837160368705 11327181125437377870276529)
          ·
            refine ⟨8495385844078033402707397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11327181125437377870276529 8495385844078033402707397)
            ·
              refine ⟨1592884845764631263007637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8495385844078033402707397 1592884845764631263007637)
              ·
                refine ⟨74666477145217090453483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1592884845764631263007637 74666477145217090453483)
                ·
                  rfl

theorem cell22_1963068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 4, 6].length) (baseStart_1963068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963068 prefixEnd_1963068 := by exact prefixLift 1963068
  have htrace : WordTrace (prefixWord ++ tailWord_1963068) baseStart_1963068 baseEnd_1963068 := by
    simpa [prefixWord, tailWord_1963068, baseEnd_1963068] using wordTrace_append hprefix tailTrace_1963068
  have hstable : (prefixWord ++ tailWord_1963068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963068).length < 2 ^ (prefixWord ++ tailWord_1963068).sum := by decide
  have hdescent : baseEnd_1963068 < baseStart_1963068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963096 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 7]
def baseStart_1963096 : Nat := 118140960795 + 1963096 * 2 ^ 59
def prefixEnd_1963096 : Nat := 4983230072969 + 3 ^ 40 * 1963096 * 2
def baseEnd_1963096 : Nat := 224002626426390358127087

theorem tailTrace_1963096 : CollatzResearch.WordTrace tailWord_1963096 prefixEnd_1963096 224002626426390358127087 := by
  unfold tailWord_1963096
  simp only [CollatzResearch.WordTrace]
  refine ⟨35799996648022968474846571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47733328864030624633128761 35799996648022968474846571)
  ·
    refine ⟨53699994972034452712269857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35799996648022968474846571 53699994972034452712269857)
    ·
      refine ⟨40274996229025839534202393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53699994972034452712269857 40274996229025839534202393)
      ·
        refine ⟨30206247171769379650651795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40274996229025839534202393 30206247171769379650651795)
        ·
          refine ⟨45309370757654069475977693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30206247171769379650651795 45309370757654069475977693)
          ·
            refine ⟨16991014034120276053491635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45309370757654069475977693 16991014034120276053491635)
            ·
              refine ⟨25486521051180414080237453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16991014034120276053491635 25486521051180414080237453)
              ·
                refine ⟨9557445394192655280089045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25486521051180414080237453 9557445394192655280089045)
                ·
                  refine ⟨224002626426390358127087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9557445394192655280089045 224002626426390358127087)
                  ·
                    rfl

theorem cell22_1963096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 7].length) (baseStart_1963096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963096 prefixEnd_1963096 := by exact prefixLift 1963096
  have htrace : WordTrace (prefixWord ++ tailWord_1963096) baseStart_1963096 baseEnd_1963096 := by
    simpa [prefixWord, tailWord_1963096, baseEnd_1963096] using wordTrace_append hprefix tailTrace_1963096
  have hstable : (prefixWord ++ tailWord_1963096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963096).length < 2 ^ (prefixWord ++ tailWord_1963096).sum := by decide
  have hdescent : baseEnd_1963096 < baseStart_1963096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963102 : List Nat := [4, 4, 1, 1, 1, 2, 2, 7]
def baseStart_1963102 : Nat := 118140960795 + 1963102 * 2 ^ 59
def prefixEnd_1963102 : Nat := 4983230072969 + 3 ^ 40 * 1963102 * 2
def baseEnd_1963102 : Nat := 74667770355754339859027

theorem tailTrace_1963102 : CollatzResearch.WordTrace tailWord_1963102 prefixEnd_1963102 74667770355754339859027 := by
  unfold tailWord_1963102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8950026516753024996801445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47733474756016133316274373 8950026516753024996801445)
  ·
    refine ⟨1678129971891192186900271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8950026516753024996801445 1678129971891192186900271)
    ·
      refine ⟨2517194957836788280350407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1678129971891192186900271 2517194957836788280350407)
      ·
        refine ⟨3775792436755182420525611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2517194957836788280350407 3775792436755182420525611)
        ·
          refine ⟨5663688655132773630788417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3775792436755182420525611 5663688655132773630788417)
          ·
            refine ⟨4247766491349580223091313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5663688655132773630788417 4247766491349580223091313)
            ·
              refine ⟨3185824868512185167318485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4247766491349580223091313 3185824868512185167318485)
              ·
                refine ⟨74667770355754339859027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3185824868512185167318485 74667770355754339859027)
                ·
                  rfl

theorem cell22_1963102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 7].length) (baseStart_1963102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963102 prefixEnd_1963102 := by exact prefixLift 1963102
  have htrace : WordTrace (prefixWord ++ tailWord_1963102) baseStart_1963102 baseEnd_1963102 := by
    simpa [prefixWord, tailWord_1963102, baseEnd_1963102] using wordTrace_append hprefix tailTrace_1963102
  have hstable : (prefixWord ++ tailWord_1963102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963102).length < 2 ^ (prefixWord ++ tailWord_1963102).sum := by decide
  have hdescent : baseEnd_1963102 < baseStart_1963102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963113 : List Nat := [1, 2, 1, 1, 1, 7, 1, 3, 5]
def baseStart_1963113 : Nat := 118140960795 + 1963113 * 2 ^ 59
def prefixEnd_1963113 : Nat := 4983230072969 + 3 ^ 40 * 1963113 * 2
def baseEnd_1963113 : Nat := 224004566242196232235403

theorem tailTrace_1963113 : CollatzResearch.WordTrace tailWord_1963113 prefixEnd_1963113 224004566242196232235403 := by
  unfold tailWord_1963113
  simp only [CollatzResearch.WordTrace]
  refine ⟨71600613336984348853061993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47733742224656232568707995 71600613336984348853061993)
  ·
    refine ⟨53700460002738261639796495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71600613336984348853061993 53700460002738261639796495)
    ·
      refine ⟨80550690004107392459694743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53700460002738261639796495 80550690004107392459694743)
      ·
        refine ⟨120826035006161088689542115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80550690004107392459694743 120826035006161088689542115)
        ·
          refine ⟨181239052509241633034313173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120826035006161088689542115 181239052509241633034313173)
          ·
            refine ⟨4247790293185350774241715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 181239052509241633034313173 4247790293185350774241715)
            ·
              refine ⟨6371685439778026161362573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4247790293185350774241715 6371685439778026161362573)
              ·
                refine ⟨2389382039916759810510965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6371685439778026161362573 2389382039916759810510965)
                ·
                  refine ⟨224004566242196232235403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2389382039916759810510965 224004566242196232235403)
                  ·
                    rfl

theorem cell22_1963113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 5].length) (baseStart_1963113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963113 prefixEnd_1963113 := by exact prefixLift 1963113
  have htrace : WordTrace (prefixWord ++ tailWord_1963113) baseStart_1963113 baseEnd_1963113 := by
    simpa [prefixWord, tailWord_1963113, baseEnd_1963113] using wordTrace_append hprefix tailTrace_1963113
  have hstable : (prefixWord ++ tailWord_1963113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963113).length < 2 ^ (prefixWord ++ tailWord_1963113).sum := by decide
  have hdescent : baseEnd_1963113 < baseStart_1963113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963173 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_1963173 : Nat := 118140960795 + 1963173 * 2 ^ 59
def prefixEnd_1963173 : Nat := 4983230072969 + 3 ^ 40 * 1963173 * 2
def baseEnd_1963173 : Nat := 672034237952768540206025

theorem tailTrace_1963173 : CollatzResearch.WordTrace tailWord_1963173 prefixEnd_1963173 672034237952768540206025 := by
  unfold tailWord_1963173
  simp only [CollatzResearch.WordTrace]
  refine ⟨71602801716766979100246173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47735201144511319400164115 71602801716766979100246173)
  ·
    refine ⟨26851050643787617162592315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71602801716766979100246173 26851050643787617162592315)
    ·
      refine ⟨40276575965681425743888473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26851050643787617162592315 40276575965681425743888473)
      ·
        refine ⟨30207431974261069307916355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40276575965681425743888473 30207431974261069307916355)
        ·
          refine ⟨45311147961391603961874533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30207431974261069307916355 45311147961391603961874533)
          ·
            refine ⟨8495840242760925742851475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45311147961391603961874533 8495840242760925742851475)
            ·
              refine ⟨12743760364141388614277213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8495840242760925742851475 12743760364141388614277213)
              ·
                refine ⟨4778910136553020730353955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12743760364141388614277213 4778910136553020730353955)
                ·
                  refine ⟨7168365204829531095530933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4778910136553020730353955 7168365204829531095530933)
                  ·
                    refine ⟨672034237952768540206025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7168365204829531095530933 672034237952768540206025)
                    ·
                      rfl

theorem cell22_1963173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_1963173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963173 prefixEnd_1963173 := by exact prefixLift 1963173
  have htrace : WordTrace (prefixWord ++ tailWord_1963173) baseStart_1963173 baseEnd_1963173 := by
    simpa [prefixWord, tailWord_1963173, baseEnd_1963173] using wordTrace_append hprefix tailTrace_1963173
  have hstable : (prefixWord ++ tailWord_1963173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963173).length < 2 ^ (prefixWord ++ tailWord_1963173).sum := by decide
  have hdescent : baseEnd_1963173 < baseStart_1963173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963175 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 6]
def baseStart_1963175 : Nat := 118140960795 + 1963175 * 2 ^ 59
def prefixEnd_1963175 : Nat := 4983230072969 + 3 ^ 40 * 1963175 * 2
def baseEnd_1963175 : Nat := 224011640864547067218673

theorem tailTrace_1963175 : CollatzResearch.WordTrace tailWord_1963175 prefixEnd_1963175 224011640864547067218673 := by
  unfold tailWord_1963175
  simp only [CollatzResearch.WordTrace]
  refine ⟨71602874662759733441818979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47735249775173155627879319 71602874662759733441818979)
  ·
    refine ⟨107404311994139600162728469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71602874662759733441818979 107404311994139600162728469)
    ·
      refine ⟨5034577124725293757627897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107404311994139600162728469 5034577124725293757627897)
      ·
        refine ⟨3775932843543970318220923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5034577124725293757627897 3775932843543970318220923)
        ·
          refine ⟨5663899265315955477331385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3775932843543970318220923 5663899265315955477331385)
          ·
            refine ⟨4247924448986966607998539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5663899265315955477331385 4247924448986966607998539)
            ·
              refine ⟨6371886673480449911997809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4247924448986966607998539 6371886673480449911997809)
              ·
                refine ⟨4778915005110337433998357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6371886673480449911997809 4778915005110337433998357)
                ·
                  refine ⟨224011640864547067218673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4778915005110337433998357 224011640864547067218673)
                  ·
                    rfl

theorem cell22_1963175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 6].length) (baseStart_1963175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963175 prefixEnd_1963175 := by exact prefixLift 1963175
  have htrace : WordTrace (prefixWord ++ tailWord_1963175) baseStart_1963175 baseEnd_1963175 := by
    simpa [prefixWord, tailWord_1963175, baseEnd_1963175] using wordTrace_append hprefix tailTrace_1963175
  have hstable : (prefixWord ++ tailWord_1963175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963175).length < 2 ^ (prefixWord ++ tailWord_1963175).sum := by decide
  have hdescent : baseEnd_1963175 < baseStart_1963175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963224 : List Nat := [2, 1, 2, 2, 5, 1, 3, 1, 2, 3]
def baseStart_1963224 : Nat := 118140960795 + 1963224 * 2 ^ 59
def prefixEnd_1963224 : Nat := 4983230072969 + 3 ^ 40 * 1963224 * 2
def baseEnd_1963224 : Nat := 672051696295021407180869

theorem tailTrace_1963224 : CollatzResearch.WordTrace tailWord_1963224 prefixEnd_1963224 672051696295021407180869 := by
  unfold tailWord_1963224
  simp only [CollatzResearch.WordTrace]
  refine ⟨35802330919791107405176363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47736441226388143206901817 35802330919791107405176363)
  ·
    refine ⟨53703496379686661107764545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35802330919791107405176363 53703496379686661107764545)
    ·
      refine ⟨40277622284764995830823409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53703496379686661107764545 40277622284764995830823409)
      ·
        refine ⟨30208216713573746873117557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40277622284764995830823409 30208216713573746873117557)
        ·
          refine ⟨2832020316897538769354771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30208216713573746873117557 2832020316897538769354771)
          ·
            refine ⟨4248030475346308154032157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2832020316897538769354771 4248030475346308154032157)
            ·
              refine ⟨1593011428254865557762059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4248030475346308154032157 1593011428254865557762059)
              ·
                refine ⟨2389517142382298336643089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593011428254865557762059 2389517142382298336643089)
                ·
                  refine ⟨1792137856786723752482317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2389517142382298336643089 1792137856786723752482317)
                  ·
                    refine ⟨672051696295021407180869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1792137856786723752482317 672051696295021407180869)
                    ·
                      rfl

theorem cell22_1963224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_1963224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963224 prefixEnd_1963224 := by exact prefixLift 1963224
  have htrace : WordTrace (prefixWord ++ tailWord_1963224) baseStart_1963224 baseEnd_1963224 := by
    simpa [prefixWord, tailWord_1963224, baseEnd_1963224] using wordTrace_append hprefix tailTrace_1963224
  have hstable : (prefixWord ++ tailWord_1963224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963224).length < 2 ^ (prefixWord ++ tailWord_1963224).sum := by decide
  have hdescent : baseEnd_1963224 < baseStart_1963224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963237 : List Nat := [1, 3, 1, 4, 3, 2, 2, 6]
def baseStart_1963237 : Nat := 118140960795 + 1963237 * 2 ^ 59
def prefixEnd_1963237 : Nat := 4983230072969 + 3 ^ 40 * 1963237 * 2
def baseEnd_1963237 : Nat := 74672905162299300733981

theorem tailTrace_1963237 : CollatzResearch.WordTrace tailWord_1963237 prefixEnd_1963237 74672905162299300733981 := by
  unfold tailWord_1963237
  simp only [CollatzResearch.WordTrace]
  refine ⟨71605135988535118030575965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47736757325690078687050643 71605135988535118030575965)
  ·
    refine ⟨26851925995700669261465987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71605135988535118030575965 26851925995700669261465987)
    ·
      refine ⟨40277888993551003892198981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26851925995700669261465987 40277888993551003892198981)
      ·
        refine ⟨7552104186290813229787309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40277888993551003892198981 7552104186290813229787309)
        ·
          refine ⟨2832039069859054961170241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7552104186290813229787309 2832039069859054961170241)
          ·
            refine ⟨2124029302394291220877681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2832039069859054961170241 2124029302394291220877681)
            ·
              refine ⟨1593021976795718415658261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2124029302394291220877681 1593021976795718415658261)
              ·
                refine ⟨74672905162299300733981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1593021976795718415658261 74672905162299300733981)
                ·
                  rfl

theorem cell22_1963237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 6].length) (baseStart_1963237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963237 prefixEnd_1963237 := by exact prefixLift 1963237
  have htrace : WordTrace (prefixWord ++ tailWord_1963237) baseStart_1963237 baseEnd_1963237 := by
    simpa [prefixWord, tailWord_1963237, baseEnd_1963237] using wordTrace_append hprefix tailTrace_1963237
  have hstable : (prefixWord ++ tailWord_1963237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963237).length < 2 ^ (prefixWord ++ tailWord_1963237).sum := by decide
  have hdescent : baseEnd_1963237 < baseStart_1963237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963269 : List Nat := [1, 3, 1, 1, 2, 1, 7, 2, 1, 3]
def baseStart_1963269 : Nat := 118140960795 + 1963269 * 2 ^ 59
def prefixEnd_1963269 : Nat := 4983230072969 + 3 ^ 40 * 1963269 * 2
def baseEnd_1963269 : Nat := 672067100714656289805731

theorem tailTrace_1963269 : CollatzResearch.WordTrace tailWord_1963269 prefixEnd_1963269 672067100714656289805731 := by
  unfold tailWord_1963269
  simp only [CollatzResearch.WordTrace]
  refine ⟨71606303124419187495740861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47737535416279458330493907 71606303124419187495740861)
  ·
    refine ⟨26852363671657195310902823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71606303124419187495740861 26852363671657195310902823)
    ·
      refine ⟨40278545507485792966354235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26852363671657195310902823 40278545507485792966354235)
      ·
        refine ⟨60417818261228689449531353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40278545507485792966354235 60417818261228689449531353)
        ·
          refine ⟨45313363695921517087148515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60417818261228689449531353 45313363695921517087148515)
          ·
            refine ⟨67970045543882275630722773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45313363695921517087148515 67970045543882275630722773)
            ·
              refine ⟨1593047942434740835095065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 67970045543882275630722773 1593047942434740835095065)
              ·
                refine ⟨1194785956826055626321299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1593047942434740835095065 1194785956826055626321299)
                ·
                  refine ⟨1792178935239083439481949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194785956826055626321299 1792178935239083439481949)
                  ·
                    refine ⟨672067100714656289805731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1792178935239083439481949 672067100714656289805731)
                    ·
                      rfl

theorem cell22_1963269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_1963269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963269 prefixEnd_1963269 := by exact prefixLift 1963269
  have htrace : WordTrace (prefixWord ++ tailWord_1963269) baseStart_1963269 baseEnd_1963269 := by
    simpa [prefixWord, tailWord_1963269, baseEnd_1963269] using wordTrace_append hprefix tailTrace_1963269
  have hstable : (prefixWord ++ tailWord_1963269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963269).length < 2 ^ (prefixWord ++ tailWord_1963269).sum := by decide
  have hdescent : baseEnd_1963269 < baseStart_1963269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963312 : List Nat := [2, 1, 1, 1, 2, 2, 7, 1, 1, 4]
def baseStart_1963312 : Nat := 118140960795 + 1963312 * 2 ^ 59
def prefixEnd_1963312 : Nat := 4983230072969 + 3 ^ 40 * 1963312 * 2
def baseEnd_1963312 : Nat := 672081820493418510980599

theorem tailTrace_1963312 : CollatzResearch.WordTrace tailWord_1963312 prefixEnd_1963312 672081820493418510980599 := by
  unfold tailWord_1963312
  simp only [CollatzResearch.WordTrace]
  refine ⟨35803935731631702919778095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47738580975508937226370793 35803935731631702919778095)
  ·
    refine ⟨53705903597447554379667143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35803935731631702919778095 53705903597447554379667143)
    ·
      refine ⟨80558855396171331569500715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53705903597447554379667143 80558855396171331569500715)
      ·
        refine ⟨120838283094256997354251073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80558855396171331569500715 120838283094256997354251073)
        ·
          refine ⟨90628712320692748015688305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120838283094256997354251073 90628712320692748015688305)
          ·
            refine ⟨67971534240519561011766229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90628712320692748015688305 67971534240519561011766229)
            ·
              refine ⟨1593082833762177211213271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 67971534240519561011766229 1593082833762177211213271)
              ·
                refine ⟨2389624250643265816819907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593082833762177211213271 2389624250643265816819907)
                ·
                  refine ⟨3584436375964898725229861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2389624250643265816819907 3584436375964898725229861)
                  ·
                    refine ⟨672081820493418510980599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3584436375964898725229861 672081820493418510980599)
                    ·
                      rfl

theorem cell22_1963312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 1, 4].length) (baseStart_1963312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963312 prefixEnd_1963312 := by exact prefixLift 1963312
  have htrace : WordTrace (prefixWord ++ tailWord_1963312) baseStart_1963312 baseEnd_1963312 := by
    simpa [prefixWord, tailWord_1963312, baseEnd_1963312] using wordTrace_append hprefix tailTrace_1963312
  have hstable : (prefixWord ++ tailWord_1963312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963312).length < 2 ^ (prefixWord ++ tailWord_1963312).sum := by decide
  have hdescent : baseEnd_1963312 < baseStart_1963312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963327 : List Nat := [1, 1, 2, 2, 4, 3, 1, 4, 4]
def baseStart_1963327 : Nat := 118140960795 + 1963327 * 2 ^ 59
def prefixEnd_1963327 : Nat := 4983230072969 + 3 ^ 40 * 1963327 * 2
def baseEnd_1963327 : Nat := 224028985099987823951851

theorem tailTrace_1963327 : CollatzResearch.WordTrace tailWord_1963327 prefixEnd_1963327 224028985099987823951851 := by
  unfold tailWord_1963327
  simp only [CollatzResearch.WordTrace]
  refine ⟨71608418558209063401352235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47738945705472708934234823 71608418558209063401352235)
  ·
    refine ⟨107412627837313595102028353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71608418558209063401352235 107412627837313595102028353)
    ·
      refine ⟨80559470877985196326521265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107412627837313595102028353 80559470877985196326521265)
      ·
        refine ⟨60419603158488897244890949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80559470877985196326521265 60419603158488897244890949)
        ·
          refine ⟨11328675592216668233417053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60419603158488897244890949 11328675592216668233417053)
          ·
            refine ⟨4248253347081250587531395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11328675592216668233417053 4248253347081250587531395)
            ·
              refine ⟨6372380020621875881297093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4248253347081250587531395 6372380020621875881297093)
              ·
                refine ⟨1194821253866601727743205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6372380020621875881297093 1194821253866601727743205)
                ·
                  refine ⟨224028985099987823951851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1194821253866601727743205 224028985099987823951851)
                  ·
                    rfl

theorem cell22_1963327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 4].length) (baseStart_1963327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963327 prefixEnd_1963327 := by exact prefixLift 1963327
  have htrace : WordTrace (prefixWord ++ tailWord_1963327) baseStart_1963327 baseEnd_1963327 := by
    simpa [prefixWord, tailWord_1963327, baseEnd_1963327] using wordTrace_append hprefix tailTrace_1963327
  have hstable : (prefixWord ++ tailWord_1963327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963327).length < 2 ^ (prefixWord ++ tailWord_1963327).sum := by decide
  have hdescent : baseEnd_1963327 < baseStart_1963327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963342 : List Nat := [4, 1, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_1963342 : Nat := 118140960795 + 1963342 * 2 ^ 59
def prefixEnd_1963342 : Nat := 4983230072969 + 3 ^ 40 * 1963342 * 2
def baseEnd_1963342 : Nat := 672092090106508432730507

theorem tailTrace_1963342 : CollatzResearch.WordTrace tailWord_1963342 prefixEnd_1963342 672092090106508432730507 := by
  unfold tailWord_1963342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8951120706644340120393535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47739310435436480642098853 8951120706644340120393535)
  ·
    refine ⟨13426681059966510180590303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8951120706644340120393535 13426681059966510180590303)
    ·
      refine ⟨20140021589949765270885455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13426681059966510180590303 20140021589949765270885455)
      ·
        refine ⟨30210032384924647906328183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20140021589949765270885455 30210032384924647906328183)
        ·
          refine ⟨45315048577386971859492275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30210032384924647906328183 45315048577386971859492275)
          ·
            refine ⟨67972572866080457789238413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45315048577386971859492275 67972572866080457789238413)
            ·
              refine ⟨25489714824780171670964405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67972572866080457789238413 25489714824780171670964405)
              ·
                refine ⟨2389660764823141094152913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25489714824780171670964405 2389660764823141094152913)
                ·
                  refine ⟨1792245573617355820614685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2389660764823141094152913 1792245573617355820614685)
                  ·
                    refine ⟨672092090106508432730507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1792245573617355820614685 672092090106508432730507)
                    ·
                      rfl

theorem cell22_1963342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_1963342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963342 prefixEnd_1963342 := by exact prefixLift 1963342
  have htrace : WordTrace (prefixWord ++ tailWord_1963342) baseStart_1963342 baseEnd_1963342 := by
    simpa [prefixWord, tailWord_1963342, baseEnd_1963342] using wordTrace_append hprefix tailTrace_1963342
  have hstable : (prefixWord ++ tailWord_1963342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963342).length < 2 ^ (prefixWord ++ tailWord_1963342).sum := by decide
  have hdescent : baseEnd_1963342 < baseStart_1963342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963387 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 3, 3]
def baseStart_1963387 : Nat := 118140960795 + 1963387 * 2 ^ 59
def prefixEnd_1963387 : Nat := 4983230072969 + 3 ^ 40 * 1963387 * 2
def baseEnd_1963387 : Nat := 672107494526143315355369

theorem tailTrace_1963387 : CollatzResearch.WordTrace tailWord_1963387 prefixEnd_1963387 672107494526143315355369 := by
  unfold tailWord_1963387
  simp only [CollatzResearch.WordTrace]
  refine ⟨71610606937991693648536415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47740404625327795765690943 71610606937991693648536415)
  ·
    refine ⟨107415910406987540472804623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71610606937991693648536415 107415910406987540472804623)
    ·
      refine ⟨161123865610481310709206935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107415910406987540472804623 161123865610481310709206935)
      ·
        refine ⟨241685798415721966063810403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161123865610481310709206935 241685798415721966063810403)
        ·
          refine ⟨362528697623582949095715605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241685798415721966063810403 362528697623582949095715605)
          ·
            refine ⟨16993532701105450738861669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 362528697623582949095715605 16993532701105450738861669)
            ·
              refine ⟨3186287381457272013536563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16993532701105450738861669 3186287381457272013536563)
              ·
                refine ⟨4779431072185908020304845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186287381457272013536563 4779431072185908020304845)
                ·
                  refine ⟨1792286652069715507614317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4779431072185908020304845 1792286652069715507614317)
                  ·
                    refine ⟨672107494526143315355369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1792286652069715507614317 672107494526143315355369)
                    ·
                      rfl

theorem cell22_1963387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 3].length) (baseStart_1963387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963387 prefixEnd_1963387 := by exact prefixLift 1963387
  have htrace : WordTrace (prefixWord ++ tailWord_1963387) baseStart_1963387 baseEnd_1963387 := by
    simpa [prefixWord, tailWord_1963387, baseEnd_1963387] using wordTrace_append hprefix tailTrace_1963387
  have hstable : (prefixWord ++ tailWord_1963387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963387).length < 2 ^ (prefixWord ++ tailWord_1963387).sum := by decide
  have hdescent : baseEnd_1963387 < baseStart_1963387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963406 : List Nat := [4, 1, 1, 4, 3, 1, 2, 6]
def baseStart_1963406 : Nat := 118140960795 + 1963406 * 2 ^ 59
def prefixEnd_1963406 : Nat := 4983230072969 + 3 ^ 40 * 1963406 * 2
def baseEnd_1963406 : Nat := 74679333179381511014479

theorem tailTrace_1963406 : CollatzResearch.WordTrace tailWord_1963406 prefixEnd_1963406 74679333179381511014479 := by
  unfold tailWord_1963406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8951412490615357486684759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47740866616615239928985381 8951412490615357486684759)
  ·
    refine ⟨13427118735923036230027139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8951412490615357486684759 13427118735923036230027139)
    ·
      refine ⟨20140678103884554345040709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13427118735923036230027139 20140678103884554345040709)
      ·
        refine ⟨3776377144478353939695133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20140678103884554345040709 3776377144478353939695133)
        ·
          refine ⟨1416141429179382727385675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3776377144478353939695133 1416141429179382727385675)
          ·
            refine ⟨2124212143769074091078513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416141429179382727385675 2124212143769074091078513)
            ·
              refine ⟨1593159107826805568308885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2124212143769074091078513 1593159107826805568308885)
              ·
                refine ⟨74679333179381511014479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1593159107826805568308885 74679333179381511014479)
                ·
                  rfl

theorem cell22_1963406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_1963406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963406 prefixEnd_1963406 := by exact prefixLift 1963406
  have htrace : WordTrace (prefixWord ++ tailWord_1963406) baseStart_1963406 baseEnd_1963406 := by
    simpa [prefixWord, tailWord_1963406, baseEnd_1963406] using wordTrace_append hprefix tailTrace_1963406
  have hstable : (prefixWord ++ tailWord_1963406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963406).length < 2 ^ (prefixWord ++ tailWord_1963406).sum := by decide
  have hdescent : baseEnd_1963406 < baseStart_1963406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963421 : List Nat := [1, 4, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_1963421 : Nat := 118140960795 + 1963421 * 2 ^ 59
def prefixEnd_1963421 : Nat := 4983230072969 + 3 ^ 40 * 1963421 * 2
def baseEnd_1963421 : Nat := 672119133420978560005265

theorem tailTrace_1963421 : CollatzResearch.WordTrace tailWord_1963421 prefixEnd_1963421 672119133420978560005265 := by
  unfold tailWord_1963421
  simp only [CollatzResearch.WordTrace]
  refine ⟨71611847019868517455274117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47741231346579011636849411 71611847019868517455274117)
  ·
    refine ⟨13427221316225347022863897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71611847019868517455274117 13427221316225347022863897)
    ·
      refine ⟨10070415987169010267147923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13427221316225347022863897 10070415987169010267147923)
      ·
        refine ⟨15105623980753515400721885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10070415987169010267147923 15105623980753515400721885)
        ·
          refine ⟨5664608992782568275270707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15105623980753515400721885 5664608992782568275270707)
          ·
            refine ⟨8496913489173852412906061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5664608992782568275270707 8496913489173852412906061)
            ·
              refine ⟨3186342558440194654839773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8496913489173852412906061 3186342558440194654839773)
              ·
                refine ⟨1194878459415072995564915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3186342558440194654839773 1194878459415072995564915)
                ·
                  refine ⟨1792317689122609493347373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1194878459415072995564915 1792317689122609493347373)
                  ·
                    refine ⟨672119133420978560005265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1792317689122609493347373 672119133420978560005265)
                    ·
                      rfl

theorem cell22_1963421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_1963421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963421 prefixEnd_1963421 := by exact prefixLift 1963421
  have htrace : WordTrace (prefixWord ++ tailWord_1963421) baseStart_1963421 baseEnd_1963421 := by
    simpa [prefixWord, tailWord_1963421, baseEnd_1963421] using wordTrace_append hprefix tailTrace_1963421
  have hstable : (prefixWord ++ tailWord_1963421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963421).length < 2 ^ (prefixWord ++ tailWord_1963421).sum := by decide
  have hdescent : baseEnd_1963421 < baseStart_1963421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963477 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_1963477 : Nat := 118140960795 + 1963477 * 2 ^ 59
def prefixEnd_1963477 : Nat := 4983230072969 + 3 ^ 40 * 1963477 * 2
def baseEnd_1963477 : Nat := 672138303365413080605093

theorem tailTrace_1963477 : CollatzResearch.WordTrace tailWord_1963477 prefixEnd_1963477 672138303365413080605093 := by
  unfold tailWord_1963477
  simp only [CollatzResearch.WordTrace]
  refine ⟨71613889507665639019312685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47742593005110426012875123 71613889507665639019312685)
  ·
    refine ⟨26855208565374614632242257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71613889507665639019312685 26855208565374614632242257)
    ·
      refine ⟨20141406424030960974181693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26855208565374614632242257 20141406424030960974181693)
      ·
        refine ⟨7553027409011610365318135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20141406424030960974181693 7553027409011610365318135)
        ·
          refine ⟨11329541113517415547977203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7553027409011610365318135 11329541113517415547977203)
          ·
            refine ⟨16994311670276123321965805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11329541113517415547977203 16994311670276123321965805)
            ·
              refine ⟨6372866876353546245737177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16994311670276123321965805 6372866876353546245737177)
              ·
                refine ⟨4779650157265159684302883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6372866876353546245737177 4779650157265159684302883)
                ·
                  refine ⟨7169475235897739526454325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4779650157265159684302883 7169475235897739526454325)
                  ·
                    refine ⟨672138303365413080605093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7169475235897739526454325 672138303365413080605093)
                    ·
                      rfl

theorem cell22_1963477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_1963477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963477 prefixEnd_1963477 := by exact prefixLift 1963477
  have htrace : WordTrace (prefixWord ++ tailWord_1963477) baseStart_1963477 baseEnd_1963477 := by
    simpa [prefixWord, tailWord_1963477, baseEnd_1963477] using wordTrace_append hprefix tailTrace_1963477
  have hstable : (prefixWord ++ tailWord_1963477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963477).length < 2 ^ (prefixWord ++ tailWord_1963477).sum := by decide
  have hdescent : baseEnd_1963477 < baseStart_1963477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963676 : List Nat := [2, 2, 3, 2, 3, 2, 1, 7]
def baseStart_1963676 : Nat := 118140960795 + 1963676 * 2 ^ 59
def prefixEnd_1963676 : Nat := 4983230072969 + 3 ^ 40 * 1963676 * 2
def baseEnd_1963676 : Nat := 74689602792471432764387

theorem tailTrace_1963676 : CollatzResearch.WordTrace tailWord_1963676 prefixEnd_1963676 74689602792471432764387 := by
  unfold tailWord_1963676
  simp only [CollatzResearch.WordTrace]
  refine ⟨35810573816972348002903441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47747431755963130670537921 35810573816972348002903441)
  ·
    refine ⟨26857930362729261002177581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35810573816972348002903441 26857930362729261002177581)
    ·
      refine ⟨10071723886023472875816593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26857930362729261002177581 10071723886023472875816593)
      ·
        refine ⟨7553792914517604656862445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10071723886023472875816593 7553792914517604656862445)
        ·
          refine ⟨2832672342944101746323417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7553792914517604656862445 2832672342944101746323417)
          ·
            refine ⟨2124504257208076309742563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2832672342944101746323417 2124504257208076309742563)
            ·
              refine ⟨3186756385812114464613845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124504257208076309742563 3186756385812114464613845)
              ·
                refine ⟨74689602792471432764387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3186756385812114464613845 74689602792471432764387)
                ·
                  rfl

theorem cell22_1963676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 7].length) (baseStart_1963676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963676 prefixEnd_1963676 := by exact prefixLift 1963676
  have htrace : WordTrace (prefixWord ++ tailWord_1963676) baseStart_1963676 baseEnd_1963676 := by
    simpa [prefixWord, tailWord_1963676, baseEnd_1963676] using wordTrace_append hprefix tailTrace_1963676
  have hstable : (prefixWord ++ tailWord_1963676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963676).length < 2 ^ (prefixWord ++ tailWord_1963676).sum := by decide
  have hdescent : baseEnd_1963676 < baseStart_1963676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963708 : List Nat := [2, 2, 2, 3, 1, 2, 1, 5, 1, 3]
def baseStart_1963708 : Nat := 118140960795 + 1963708 * 2 ^ 59
def prefixEnd_1963708 : Nat := 4983230072969 + 3 ^ 40 * 1963708 * 2
def baseEnd_1963708 : Nat := 672217379386205478079385

theorem tailTrace_1963708 : CollatzResearch.WordTrace tailWord_1963708 prefixEnd_1963708 672217379386205478079385 := by
  unfold tailWord_1963708
  simp only [CollatzResearch.WordTrace]
  refine ⟨35811157384914382735485889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47748209846552510313981185 35811157384914382735485889)
  ·
    refine ⟨26858368038685787051614417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35811157384914382735485889 26858368038685787051614417)
    ·
      refine ⟨20143776029014340288710813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26858368038685787051614417 20143776029014340288710813)
      ·
        refine ⟨7553916010880377608266555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20143776029014340288710813 7553916010880377608266555)
        ·
          refine ⟨11330874016320566412399833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7553916010880377608266555 11330874016320566412399833)
          ·
            refine ⟨8498155512240424809299875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11330874016320566412399833 8498155512240424809299875)
            ·
              refine ⟨12747233268360637213949813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8498155512240424809299875 12747233268360637213949813)
              ·
                refine ⟨1195053118908809738807795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12747233268360637213949813 1195053118908809738807795)
                ·
                  refine ⟨1792579678363214608211693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195053118908809738807795 1792579678363214608211693)
                  ·
                    refine ⟨672217379386205478079385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1792579678363214608211693 672217379386205478079385)
                    ·
                      rfl

theorem cell22_1963708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_1963708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963708 prefixEnd_1963708 := by exact prefixLift 1963708
  have htrace : WordTrace (prefixWord ++ tailWord_1963708) baseStart_1963708 baseEnd_1963708 := by
    simpa [prefixWord, tailWord_1963708, baseEnd_1963708] using wordTrace_append hprefix tailTrace_1963708
  have hstable : (prefixWord ++ tailWord_1963708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963708).length < 2 ^ (prefixWord ++ tailWord_1963708).sum := by decide
  have hdescent : baseEnd_1963708 < baseStart_1963708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963714 : List Nat := [3, 5, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1963714 : Nat := 118140960795 + 1963714 * 2 ^ 59
def prefixEnd_1963714 : Nat := 4983230072969 + 3 ^ 40 * 1963714 * 2
def baseEnd_1963714 : Nat := 672219433308823462429367

theorem tailTrace_1963714 : CollatzResearch.WordTrace tailWord_1963714 prefixEnd_1963714 672219433308823462429367 := by
  unfold tailWord_1963714
  simp only [CollatzResearch.WordTrace]
  refine ⟨17905633401951757123922549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47748355738538018997126797 17905633401951757123922549)
  ·
    refine ⟨1678653131432977230367739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17905633401951757123922549 1678653131432977230367739)
    ·
      refine ⟨2517979697149465845551609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1678653131432977230367739 2517979697149465845551609)
      ·
        refine ⟨1888484772862099384163707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2517979697149465845551609 1888484772862099384163707)
        ·
          refine ⟨2832727159293149076245561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1888484772862099384163707 2832727159293149076245561)
          ·
            refine ⟨2124545369469861807184171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2832727159293149076245561 2124545369469861807184171)
            ·
              refine ⟨3186818054204792710776257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124545369469861807184171 3186818054204792710776257)
              ·
                refine ⟨2390113540653594533082193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3186818054204792710776257 2390113540653594533082193)
                ·
                  refine ⟨1792585155490195899811645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2390113540653594533082193 1792585155490195899811645)
                  ·
                    refine ⟨672219433308823462429367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1792585155490195899811645 672219433308823462429367)
                    ·
                      rfl

theorem cell22_1963714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1963714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963714 prefixEnd_1963714 := by exact prefixLift 1963714
  have htrace : WordTrace (prefixWord ++ tailWord_1963714) baseStart_1963714 baseEnd_1963714 := by
    simpa [prefixWord, tailWord_1963714, baseEnd_1963714] using wordTrace_append hprefix tailTrace_1963714
  have hstable : (prefixWord ++ tailWord_1963714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963714).length < 2 ^ (prefixWord ++ tailWord_1963714).sum := by decide
  have hdescent : baseEnd_1963714 < baseStart_1963714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963725 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1963725 : Nat := 118140960795 + 1963725 * 2 ^ 59
def prefixEnd_1963725 : Nat := 4983230072969 + 3 ^ 40 * 1963725 * 2
def baseEnd_1963725 : Nat := 672223198833623100404333

theorem tailTrace_1963725 : CollatzResearch.WordTrace tailWord_1963725 prefixEnd_1963725 672223198833623100404333 := by
  unfold tailWord_1963725
  simp only [CollatzResearch.WordTrace]
  refine ⟨71622934810767177374340629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47748623207178118249560419 71622934810767177374340629)
  ·
    refine ⟨3357325069254711439422217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71622934810767177374340629 3357325069254711439422217)
    ·
      refine ⟨2517993801941033579566663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3357325069254711439422217 2517993801941033579566663)
      ·
        refine ⟨3776990702911550369349995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2517993801941033579566663 3776990702911550369349995)
        ·
          refine ⟨5665486054367325554024993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3776990702911550369349995 5665486054367325554024993)
          ·
            refine ⟨4249114540775494165518745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5665486054367325554024993 4249114540775494165518745)
            ·
              refine ⟨3186835905581620624139059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4249114540775494165518745 3186835905581620624139059)
              ·
                refine ⟨4780253858372430936208589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186835905581620624139059 4780253858372430936208589)
                ·
                  refine ⟨1792595196889661601078221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4780253858372430936208589 1792595196889661601078221)
                  ·
                    refine ⟨672223198833623100404333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1792595196889661601078221 672223198833623100404333)
                    ·
                      rfl

theorem cell22_1963725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1963725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963725 prefixEnd_1963725 := by exact prefixLift 1963725
  have htrace : WordTrace (prefixWord ++ tailWord_1963725) baseStart_1963725 baseEnd_1963725 := by
    simpa [prefixWord, tailWord_1963725, baseEnd_1963725] using wordTrace_append hprefix tailTrace_1963725
  have hstable : (prefixWord ++ tailWord_1963725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963725).length < 2 ^ (prefixWord ++ tailWord_1963725).sum := by decide
  have hdescent : baseEnd_1963725 < baseStart_1963725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963749 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 6]
def baseStart_1963749 : Nat := 118140960795 + 1963749 * 2 ^ 59
def prefixEnd_1963749 : Nat := 4983230072969 + 3 ^ 40 * 1963749 * 2
def baseEnd_1963749 : Nat := 224077138174698345934753

theorem tailTrace_1963749 : CollatzResearch.WordTrace tailWord_1963749 prefixEnd_1963749 224077138174698345934753 := by
  unfold tailWord_1963749
  simp only [CollatzResearch.WordTrace]
  refine ⟨71623810162680229473214301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47749206775120152982142867 71623810162680229473214301)
  ·
    refine ⟨26858928811005086052455363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71623810162680229473214301 26858928811005086052455363)
    ·
      refine ⟨40288393216507629078683045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26858928811005086052455363 40288393216507629078683045)
      ·
        refine ⟨7554073728095180452253071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40288393216507629078683045 7554073728095180452253071)
        ·
          refine ⟨11331110592142770678379607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7554073728095180452253071 11331110592142770678379607)
          ·
            refine ⟨16996665888214156017569411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11331110592142770678379607 16996665888214156017569411)
            ·
              refine ⟨25494998832321234026354117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16996665888214156017569411 25494998832321234026354117)
              ·
                refine ⟨4780312281060231379941397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25494998832321234026354117 4780312281060231379941397)
                ·
                  refine ⟨224077138174698345934753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4780312281060231379941397 224077138174698345934753)
                  ·
                    rfl

theorem cell22_1963749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_1963749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963749 prefixEnd_1963749 := by exact prefixLift 1963749
  have htrace : WordTrace (prefixWord ++ tailWord_1963749) baseStart_1963749 baseEnd_1963749 := by
    simpa [prefixWord, tailWord_1963749, baseEnd_1963749] using wordTrace_append hprefix tailTrace_1963749
  have hstable : (prefixWord ++ tailWord_1963749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963749).length < 2 ^ (prefixWord ++ tailWord_1963749).sum := by decide
  have hdescent : baseEnd_1963749 < baseStart_1963749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963779 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 4, 4]
def baseStart_1963779 : Nat := 118140960795 + 1963779 * 2 ^ 59
def prefixEnd_1963779 : Nat := 4983230072969 + 3 ^ 40 * 1963779 * 2
def baseEnd_1963779 : Nat := 672241684137184959554167

theorem tailTrace_1963779 : CollatzResearch.WordTrace tailWord_1963779 prefixEnd_1963779 672241684137184959554167 := by
  unfold tailWord_1963779
  simp only [CollatzResearch.WordTrace]
  refine ⟨71624904352571544596806391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47749936235047696397870927 71624904352571544596806391)
  ·
    refine ⟨107437356528857316895209587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71624904352571544596806391 107437356528857316895209587)
    ·
      refine ⟨161156034793285975342814381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107437356528857316895209587 161156034793285975342814381)
      ·
        refine ⟨60433513047482240753555393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161156034793285975342814381 60433513047482240753555393)
        ·
          refine ⟨45325134785611680565166545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60433513047482240753555393 45325134785611680565166545)
          ·
            refine ⟨33993851089208760423874909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45325134785611680565166545 33993851089208760423874909)
            ·
              refine ⟨12747694158453285158953091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33993851089208760423874909 12747694158453285158953091)
              ·
                refine ⟨19121541237679927738429637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12747694158453285158953091 19121541237679927738429637)
                ·
                  refine ⟨3585288982064986450955557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19121541237679927738429637 3585288982064986450955557)
                  ·
                    refine ⟨672241684137184959554167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3585288982064986450955557 672241684137184959554167)
                    ·
                      rfl

theorem cell22_1963779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 4].length) (baseStart_1963779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963779 prefixEnd_1963779 := by exact prefixLift 1963779
  have htrace : WordTrace (prefixWord ++ tailWord_1963779) baseStart_1963779 baseEnd_1963779 := by
    simpa [prefixWord, tailWord_1963779, baseEnd_1963779] using wordTrace_append hprefix tailTrace_1963779
  have hstable : (prefixWord ++ tailWord_1963779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963779).length < 2 ^ (prefixWord ++ tailWord_1963779).sum := by decide
  have hdescent : baseEnd_1963779 < baseStart_1963779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963783 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 6]
def baseStart_1963783 : Nat := 118140960795 + 1963783 * 2 ^ 59
def prefixEnd_1963783 : Nat := 4983230072969 + 3 ^ 40 * 1963783 * 2
def baseEnd_1963783 : Nat := 224081017806310094151385

theorem tailTrace_1963783 : CollatzResearch.WordTrace tailWord_1963783 prefixEnd_1963783 224081017806310094151385 := by
  unfold tailWord_1963783
  simp only [CollatzResearch.WordTrace]
  refine ⟨71625050244557053279952003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47750033496371368853301335 71625050244557053279952003)
  ·
    refine ⟨107437575366835579919928005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71625050244557053279952003 107437575366835579919928005)
    ·
      refine ⟨20144545381281671234986501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107437575366835579919928005 20144545381281671234986501)
      ·
        refine ⟨3777102258990313356559969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20144545381281671234986501 3777102258990313356559969)
        ·
          refine ⟨2832826694242735017419977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3777102258990313356559969 2832826694242735017419977)
          ·
            refine ⟨2124620020682051263064983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2832826694242735017419977 2124620020682051263064983)
            ·
              refine ⟨3186930031023076894597475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2124620020682051263064983 3186930031023076894597475)
              ·
                refine ⟨4780395046534615341896213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3186930031023076894597475 4780395046534615341896213)
                ·
                  refine ⟨224081017806310094151385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4780395046534615341896213 224081017806310094151385)
                  ·
                    rfl

theorem cell22_1963783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 6].length) (baseStart_1963783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963783 prefixEnd_1963783 := by exact prefixLift 1963783
  have htrace : WordTrace (prefixWord ++ tailWord_1963783) baseStart_1963783 baseEnd_1963783 := by
    simpa [prefixWord, tailWord_1963783, baseEnd_1963783] using wordTrace_append hprefix tailTrace_1963783
  have hstable : (prefixWord ++ tailWord_1963783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963783).length < 2 ^ (prefixWord ++ tailWord_1963783).sum := by decide
  have hdescent : baseEnd_1963783 < baseStart_1963783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963933 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_1963933 : Nat := 118140960795 + 1963933 * 2 ^ 59
def prefixEnd_1963933 : Nat := 4983230072969 + 3 ^ 40 * 1963933 * 2
def baseEnd_1963933 : Nat := 672294401484379891203695

theorem tailTrace_1963933 : CollatzResearch.WordTrace tailWord_1963933 prefixEnd_1963933 672294401484379891203695 := by
  unfold tailWord_1963933
  simp only [CollatzResearch.WordTrace]
  refine ⟨71630521194013628897912453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47753680796009085931941635 71630521194013628897912453)
  ·
    refine ⟨13430722723877555418358585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71630521194013628897912453 13430722723877555418358585)
    ·
      refine ⟨10073042042908166563768939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13430722723877555418358585 10073042042908166563768939)
      ·
        refine ⟨15109563064362249845653409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073042042908166563768939 15109563064362249845653409)
        ·
          refine ⟨11332172298271687384240057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15109563064362249845653409 11332172298271687384240057)
          ·
            refine ⟨8499129223703765538180043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11332172298271687384240057 8499129223703765538180043)
            ·
              refine ⟨12748693835555648307270065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8499129223703765538180043 12748693835555648307270065)
              ·
                refine ⟨9561520376666736230452549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12748693835555648307270065 9561520376666736230452549)
                ·
                  refine ⟨1792785070625013043209853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9561520376666736230452549 1792785070625013043209853)
                  ·
                    refine ⟨672294401484379891203695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1792785070625013043209853 672294401484379891203695)
                    ·
                      rfl

theorem cell22_1963933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_1963933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963933 prefixEnd_1963933 := by exact prefixLift 1963933
  have htrace : WordTrace (prefixWord ++ tailWord_1963933) baseStart_1963933 baseEnd_1963933 := by
    simpa [prefixWord, tailWord_1963933, baseEnd_1963933] using wordTrace_append hprefix tailTrace_1963933
  have hstable : (prefixWord ++ tailWord_1963933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963933).length < 2 ^ (prefixWord ++ tailWord_1963933).sum := by decide
  have hdescent : baseEnd_1963933 < baseStart_1963933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1963978 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 3, 3]
def baseStart_1963978 : Nat := 118140960795 + 1963978 * 2 ^ 59
def prefixEnd_1963978 : Nat := 4983230072969 + 3 ^ 40 * 1963978 * 2
def baseEnd_1963978 : Nat := 672309805904014773828557

theorem tailTrace_1963978 : CollatzResearch.WordTrace tailWord_1963978 prefixEnd_1963978 672309805904014773828557 := by
  unfold tailWord_1963978
  simp only [CollatzResearch.WordTrace]
  refine ⟨17908040619712650395825147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47754774985900401055533725 17908040619712650395825147)
  ·
    refine ⟨26862060929568975593737721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17908040619712650395825147 26862060929568975593737721)
    ·
      refine ⟨20146545697176731695303291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26862060929568975593737721 20146545697176731695303291)
      ·
        refine ⟨30219818545765097542954937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20146545697176731695303291 30219818545765097542954937)
        ·
          refine ⟨22664863909323823157216203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30219818545765097542954937 22664863909323823157216203)
          ·
            refine ⟨33997295863985734735824305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22664863909323823157216203 33997295863985734735824305)
            ·
              refine ⟨25497971897989301051868229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33997295863985734735824305 25497971897989301051868229)
              ·
                refine ⟨4780869730872993947225293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25497971897989301051868229 4780869730872993947225293)
                ·
                  refine ⟨1792826149077372730209485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4780869730872993947225293 1792826149077372730209485)
                  ·
                    refine ⟨672309805904014773828557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1792826149077372730209485 672309805904014773828557)
                    ·
                      rfl

theorem cell22_1963978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_1963978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1963978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1963978 prefixEnd_1963978 := by exact prefixLift 1963978
  have htrace : WordTrace (prefixWord ++ tailWord_1963978) baseStart_1963978 baseEnd_1963978 := by
    simpa [prefixWord, tailWord_1963978, baseEnd_1963978] using wordTrace_append hprefix tailTrace_1963978
  have hstable : (prefixWord ++ tailWord_1963978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1963978).length < 2 ^ (prefixWord ++ tailWord_1963978).sum := by decide
  have hdescent : baseEnd_1963978 < baseStart_1963978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1963978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964085 : List Nat := [1, 3, 3, 1, 1, 1, 2, 5, 2, 3]
def baseStart_1964085 : Nat := 118140960795 + 1964085 * 2 ^ 59
def prefixEnd_1964085 : Nat := 4983230072969 + 3 ^ 40 * 1964085 * 2
def baseEnd_1964085 : Nat := 672346434190702161403229

theorem tailTrace_1964085 : CollatzResearch.WordTrace tailWord_1964085 prefixEnd_1964085 672346434190702161403229 := by
  unfold tailWord_1964085
  simp only [CollatzResearch.WordTrace]
  refine ⟨71636065089462958857445709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47757376726308639238297139 71636065089462958857445709)
  ·
    refine ⟨26863524408548609571542141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71636065089462958857445709 26863524408548609571542141)
    ·
      refine ⟨10073821653205728589328303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26863524408548609571542141 10073821653205728589328303)
      ·
        refine ⟨15110732479808592883992455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10073821653205728589328303 15110732479808592883992455)
        ·
          refine ⟨22666098719712889325988683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15110732479808592883992455 22666098719712889325988683)
          ·
            refine ⟨33999148079569333988983025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22666098719712889325988683 33999148079569333988983025)
            ·
              refine ⟨25499361059677000491737269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33999148079569333988983025 25499361059677000491737269)
              ·
                refine ⟨2390565099344718796100369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25499361059677000491737269 2390565099344718796100369)
                ·
                  refine ⟨1792923824508539097075277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2390565099344718796100369 1792923824508539097075277)
                  ·
                    refine ⟨672346434190702161403229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1792923824508539097075277 672346434190702161403229)
                    ·
                      rfl

theorem cell22_1964085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_1964085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964085 prefixEnd_1964085 := by exact prefixLift 1964085
  have htrace : WordTrace (prefixWord ++ tailWord_1964085) baseStart_1964085 baseEnd_1964085 := by
    simpa [prefixWord, tailWord_1964085, baseEnd_1964085] using wordTrace_append hprefix tailTrace_1964085
  have hstable : (prefixWord ++ tailWord_1964085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964085).length < 2 ^ (prefixWord ++ tailWord_1964085).sum := by decide
  have hdescent : baseEnd_1964085 < baseStart_1964085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964102 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1964102 : Nat := 118140960795 + 1964102 * 2 ^ 59
def prefixEnd_1964102 : Nat := 4983230072969 + 3 ^ 40 * 1964102 * 2
def baseEnd_1964102 : Nat := 672352253638119783728177

theorem tailTrace_1964102 : CollatzResearch.WordTrace tailWord_1964102 prefixEnd_1964102 672352253638119783728177 := by
  unfold tailWord_1964102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2238646410325042836275455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47757790086934247173876373 2238646410325042836275455)
  ·
    refine ⟨3357969615487564254413183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2238646410325042836275455 3357969615487564254413183)
    ·
      refine ⟨5036954423231346381619775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3357969615487564254413183 5036954423231346381619775)
      ·
        refine ⟨7555431634847019572429663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5036954423231346381619775 7555431634847019572429663)
        ·
          refine ⟨11333147452270529358644495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7555431634847019572429663 11333147452270529358644495)
          ·
            refine ⟨16999721178405794037966743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11333147452270529358644495 16999721178405794037966743)
            ·
              refine ⟨25499581767608691056950115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16999721178405794037966743 25499581767608691056950115)
              ·
                refine ⟨38249372651413036585425173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25499581767608691056950115 38249372651413036585425173)
                ·
                  refine ⟨1792939343034986089941805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38249372651413036585425173 1792939343034986089941805)
                  ·
                    refine ⟨672352253638119783728177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1792939343034986089941805 672352253638119783728177)
                    ·
                      rfl

theorem cell22_1964102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1964102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964102 prefixEnd_1964102 := by exact prefixLift 1964102
  have htrace : WordTrace (prefixWord ++ tailWord_1964102) baseStart_1964102 baseEnd_1964102 := by
    simpa [prefixWord, tailWord_1964102, baseEnd_1964102] using wordTrace_append hprefix tailTrace_1964102
  have hstable : (prefixWord ++ tailWord_1964102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964102).length < 2 ^ (prefixWord ++ tailWord_1964102).sum := by decide
  have hdescent : baseEnd_1964102 < baseStart_1964102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964205 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 8]
def baseStart_1964205 : Nat := 118140960795 + 1964205 * 2 ^ 59
def prefixEnd_1964205 : Nat := 4983230072969 + 3 ^ 40 * 1964205 * 2
def baseEnd_1964205 : Nat := 224129170881020616134287

theorem tailTrace_1964205 : CollatzResearch.WordTrace tailWord_1964205 prefixEnd_1964205 224129170881020616134287 := by
  unfold tailWord_1964205
  simp only [CollatzResearch.WordTrace]
  refine ⟨71640441849028219351814069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47760294566018812901209379 71640441849028219351814069)
  ·
    refine ⟨6716291423346395564232569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71640441849028219351814069 6716291423346395564232569)
    ·
      refine ⟨5037218567509796673174427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6716291423346395564232569 5037218567509796673174427)
      ·
        refine ⟨7555827851264695009761641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5037218567509796673174427 7555827851264695009761641)
        ·
          refine ⟨5666870888448521257321231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7555827851264695009761641 5666870888448521257321231)
          ·
            refine ⟨8500306332672781885981847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5666870888448521257321231 8500306332672781885981847)
            ·
              refine ⟨12750459499009172828972771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8500306332672781885981847 12750459499009172828972771)
              ·
                refine ⟨19125689248513759243459157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12750459499009172828972771 19125689248513759243459157)
                ·
                  refine ⟨224129170881020616134287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19125689248513759243459157 224129170881020616134287)
                  ·
                    rfl

theorem cell22_1964205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_1964205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964205 prefixEnd_1964205 := by exact prefixLift 1964205
  have htrace : WordTrace (prefixWord ++ tailWord_1964205) baseStart_1964205 baseEnd_1964205 := by
    simpa [prefixWord, tailWord_1964205, baseEnd_1964205] using wordTrace_append hprefix tailTrace_1964205
  have hstable : (prefixWord ++ tailWord_1964205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964205).length < 2 ^ (prefixWord ++ tailWord_1964205).sum := by decide
  have hdescent : baseEnd_1964205 < baseStart_1964205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964224 : List Nat := [2, 1, 1, 2, 5, 3, 2, 1, 1, 4]
def baseStart_1964224 : Nat := 118140960795 + 1964224 * 2 ^ 59
def prefixEnd_1964224 : Nat := 4983230072969 + 3 ^ 40 * 1964224 * 2
def baseEnd_1964224 : Nat := 672394016731352132177803

theorem tailTrace_1964224 : CollatzResearch.WordTrace tailWord_1964224 prefixEnd_1964224 672394016731352132177803 := by
  unfold tailWord_1964224
  simp only [CollatzResearch.WordTrace]
  refine ⟨35820567417979692798377863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47760756557306257064503817 35820567417979692798377863)
  ·
    refine ⟨53730851126969539197566795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35820567417979692798377863 53730851126969539197566795)
    ·
      refine ⟨80596276690454308796350193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53730851126969539197566795 80596276690454308796350193)
      ·
        refine ⟨60447207517840731597262645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80596276690454308796350193 60447207517840731597262645)
        ·
          refine ⟨5666925704797568587243373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60447207517840731597262645 5666925704797568587243373)
          ·
            refine ⟨2125097139299088220216265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5666925704797568587243373 2125097139299088220216265)
            ·
              refine ⟨1593822854474316165162199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2125097139299088220216265 1593822854474316165162199)
              ·
                refine ⟨2390734281711474247743299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1593822854474316165162199 2390734281711474247743299)
                ·
                  refine ⟨3586101422567211371614949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390734281711474247743299 3586101422567211371614949)
                  ·
                    refine ⟨672394016731352132177803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3586101422567211371614949 672394016731352132177803)
                    ·
                      rfl

theorem cell22_1964224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 1, 4].length) (baseStart_1964224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964224 prefixEnd_1964224 := by exact prefixLift 1964224
  have htrace : WordTrace (prefixWord ++ tailWord_1964224) baseStart_1964224 baseEnd_1964224 := by
    simpa [prefixWord, tailWord_1964224, baseEnd_1964224] using wordTrace_append hprefix tailTrace_1964224
  have hstable : (prefixWord ++ tailWord_1964224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964224).length < 2 ^ (prefixWord ++ tailWord_1964224).sum := by decide
  have hdescent : baseEnd_1964224 < baseStart_1964224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964258 : List Nat := [3, 3, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1964258 : Nat := 118140960795 + 1964258 * 2 ^ 59
def prefixEnd_1964258 : Nat := 4983230072969 + 3 ^ 40 * 1964258 * 2
def baseEnd_1964258 : Nat := 672405655626187376827699

theorem tailTrace_1964258 : CollatzResearch.WordTrace tailWord_1964258 prefixEnd_1964258 672405655626187376827699 := by
  unfold tailWord_1964258
  simp only [CollatzResearch.WordTrace]
  refine ⟨17910593729459052350873357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47761583278557472935662285 17910593729459052350873357)
  ·
    refine ⟨6716472648547144631577509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17910593729459052350873357 6716472648547144631577509)
    ·
      refine ⟨1259338621602589618420783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6716472648547144631577509 1259338621602589618420783)
      ·
        refine ⟨1889007932403884427631175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1259338621602589618420783 1889007932403884427631175)
        ·
          refine ⟨2833511898605826641446763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1889007932403884427631175 2833511898605826641446763)
          ·
            refine ⟨4250267847908739962170145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2833511898605826641446763 4250267847908739962170145)
            ·
              refine ⟨3187700885931554971627609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4250267847908739962170145 3187700885931554971627609)
              ·
                refine ⟨2390775664448666228720707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3187700885931554971627609 2390775664448666228720707)
                ·
                  refine ⟨3586163496672999343081061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2390775664448666228720707 3586163496672999343081061)
                  ·
                    refine ⟨672405655626187376827699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3586163496672999343081061 672405655626187376827699)
                    ·
                      rfl

theorem cell22_1964258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1964258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964258 prefixEnd_1964258 := by exact prefixLift 1964258
  have htrace : WordTrace (prefixWord ++ tailWord_1964258) baseStart_1964258 baseEnd_1964258 := by
    simpa [prefixWord, tailWord_1964258, baseEnd_1964258] using wordTrace_append hprefix tailTrace_1964258
  have hstable : (prefixWord ++ tailWord_1964258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964258).length < 2 ^ (prefixWord ++ tailWord_1964258).sum := by decide
  have hdescent : baseEnd_1964258 < baseStart_1964258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964372 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_1964372 : Nat := 118140960795 + 1964372 * 2 ^ 59
def prefixEnd_1964372 : Nat := 4983230072969 + 3 ^ 40 * 1964372 * 2
def baseEnd_1964372 : Nat := 672444680155929079477349

theorem tailTrace_1964372 : CollatzResearch.WordTrace tailWord_1964372 prefixEnd_1964372 672444680155929079477349 := by
  unfold tailWord_1964372
  simp only [CollatzResearch.WordTrace]
  refine ⟨35823266419711603436571685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47764355226282137915428913 35823266419711603436571685)
  ·
    refine ⟨6716862453695925644357191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35823266419711603436571685 6716862453695925644357191)
    ·
      refine ⟨10075293680543888466535787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6716862453695925644357191 10075293680543888466535787)
      ·
        refine ⟨15112940520815832699803681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10075293680543888466535787 15112940520815832699803681)
        ·
          refine ⟨11334705390611874524852761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15112940520815832699803681 11334705390611874524852761)
          ·
            refine ⟨8501029042958905893639571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11334705390611874524852761 8501029042958905893639571)
            ·
              refine ⟨12751543564438358840459357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8501029042958905893639571 12751543564438358840459357)
              ·
                refine ⟨4781828836664384565172259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12751543564438358840459357 4781828836664384565172259)
                ·
                  refine ⟨7172743254996576847758389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4781828836664384565172259 7172743254996576847758389)
                  ·
                    refine ⟨672444680155929079477349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7172743254996576847758389 672444680155929079477349)
                    ·
                      rfl

theorem cell22_1964372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_1964372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964372 prefixEnd_1964372 := by exact prefixLift 1964372
  have htrace : WordTrace (prefixWord ++ tailWord_1964372) baseStart_1964372 baseEnd_1964372 := by
    simpa [prefixWord, tailWord_1964372, baseEnd_1964372] using wordTrace_append hprefix tailTrace_1964372
  have hstable : (prefixWord ++ tailWord_1964372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964372).length < 2 ^ (prefixWord ++ tailWord_1964372).sum := by decide
  have hdescent : baseEnd_1964372 < baseStart_1964372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964436 : List Nat := [2, 4, 2, 1, 3, 2, 2, 6]
def baseStart_1964436 : Nat := 118140960795 + 1964436 * 2 ^ 59
def prefixEnd_1964436 : Nat := 4983230072969 + 3 ^ 40 * 1964436 * 2
def baseEnd_1964436 : Nat := 74718509851539360653017

theorem tailTrace_1964436 : CollatzResearch.WordTrace tailWord_1964436 prefixEnd_1964436 74718509851539360653017 := by
  unfold tailWord_1964436
  simp only [CollatzResearch.WordTrace]
  refine ⟨35824433555595672901736581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47765911407460897202315441 35824433555595672901736581)
  ·
    refine ⟨6717081291674188669075609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35824433555595672901736581 6717081291674188669075609)
    ·
      refine ⟨5037810968755641501806707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6717081291674188669075609 5037810968755641501806707)
      ·
        refine ⟨7556716453133462252710061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5037810968755641501806707 7556716453133462252710061)
        ·
          refine ⟨2833768669925048344766273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7556716453133462252710061 2833768669925048344766273)
          ·
            refine ⟨2125326502443786258574705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2833768669925048344766273 2125326502443786258574705)
            ·
              refine ⟨1593994876832839693931029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2125326502443786258574705 1593994876832839693931029)
              ·
                refine ⟨74718509851539360653017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1593994876832839693931029 74718509851539360653017)
                ·
                  rfl

theorem cell22_1964436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 6].length) (baseStart_1964436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964436 prefixEnd_1964436 := by exact prefixLift 1964436
  have htrace : WordTrace (prefixWord ++ tailWord_1964436) baseStart_1964436 baseEnd_1964436 := by
    simpa [prefixWord, tailWord_1964436, baseEnd_1964436] using wordTrace_append hprefix tailTrace_1964436
  have hstable : (prefixWord ++ tailWord_1964436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964436).length < 2 ^ (prefixWord ++ tailWord_1964436).sum := by decide
  have hdescent : baseEnd_1964436 < baseStart_1964436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964451 : List Nat := [1, 1, 1, 4, 1, 4, 3, 3, 1, 3]
def baseStart_1964451 : Nat := 118140960795 + 1964451 * 2 ^ 59
def prefixEnd_1964451 : Nat := 4983230072969 + 3 ^ 40 * 1964451 * 2
def baseEnd_1964451 : Nat := 672471723470399206752107

theorem tailTrace_1964451 : CollatzResearch.WordTrace tailWord_1964451 prefixEnd_1964451 672471723470399206752107 := by
  unfold tailWord_1964451
  simp only [CollatzResearch.WordTrace]
  refine ⟨71649414206137003365269207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47766276137424668910179471 71649414206137003365269207)
  ·
    refine ⟨107474121309205505047903811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71649414206137003365269207 107474121309205505047903811)
    ·
      refine ⟨161211181963808257571855717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107474121309205505047903811 161211181963808257571855717)
      ·
        refine ⟨30227096618214048294722947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161211181963808257571855717 30227096618214048294722947)
        ·
          refine ⟨45340644927321072442084421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30227096618214048294722947 45340644927321072442084421)
          ·
            refine ⟨8501370923872701082890829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45340644927321072442084421 8501370923872701082890829)
            ·
              refine ⟨3188014096452262906084061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8501370923872701082890829 3188014096452262906084061)
              ·
                refine ⟨1195505286169598589781523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3188014096452262906084061 1195505286169598589781523)
                ·
                  refine ⟨1793257929254397884672285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195505286169598589781523 1793257929254397884672285)
                  ·
                    refine ⟨672471723470399206752107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1793257929254397884672285 672471723470399206752107)
                    ·
                      rfl

theorem cell22_1964451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 1, 3].length) (baseStart_1964451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964451 prefixEnd_1964451 := by exact prefixLift 1964451
  have htrace : WordTrace (prefixWord ++ tailWord_1964451) baseStart_1964451 baseEnd_1964451 := by
    simpa [prefixWord, tailWord_1964451, baseEnd_1964451] using wordTrace_append hprefix tailTrace_1964451
  have hstable : (prefixWord ++ tailWord_1964451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964451).length < 2 ^ (prefixWord ++ tailWord_1964451).sum := by decide
  have hdescent : baseEnd_1964451 < baseStart_1964451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964475 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 12]
def baseStart_1964475 : Nat := 118140960795 + 1964475 * 2 ^ 59
def prefixEnd_1964475 : Nat := 4983230072969 + 3 ^ 40 * 1964475 * 2
def baseEnd_1964475 : Nat := 224159979720290381384011

theorem tailTrace_1964475 : CollatzResearch.WordTrace tailWord_1964475 prefixEnd_1964475 224159979720290381384011 := by
  unfold tailWord_1964475
  simp only [CollatzResearch.WordTrace]
  refine ⟨71650289558050055464142879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47766859705366703642761919 71650289558050055464142879)
  ·
    refine ⟨107475434337075083196214319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71650289558050055464142879 107475434337075083196214319)
    ·
      refine ⟨161213151505612624794321479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107475434337075083196214319 161213151505612624794321479)
      ·
        refine ⟨241819727258418937191482219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161213151505612624794321479 241819727258418937191482219)
        ·
          refine ⟨362729590887628405787223329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241819727258418937191482219 362729590887628405787223329)
          ·
            refine ⟨272047193165721304340417497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362729590887628405787223329 272047193165721304340417497)
            ·
              refine ⟨204035394874290978255313123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272047193165721304340417497 204035394874290978255313123)
              ·
                refine ⟨306053092311436467382969685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204035394874290978255313123 306053092311436467382969685)
                ·
                  refine ⟨224159979720290381384011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 306053092311436467382969685 224159979720290381384011)
                  ·
                    rfl

theorem cell22_1964475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 12].length) (baseStart_1964475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964475 prefixEnd_1964475 := by exact prefixLift 1964475
  have htrace : WordTrace (prefixWord ++ tailWord_1964475) baseStart_1964475 baseEnd_1964475 := by
    simpa [prefixWord, tailWord_1964475, baseEnd_1964475] using wordTrace_append hprefix tailTrace_1964475
  have hstable : (prefixWord ++ tailWord_1964475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964475).length < 2 ^ (prefixWord ++ tailWord_1964475).sum := by decide
  have hdescent : baseEnd_1964475 < baseStart_1964475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964511 : List Nat := [1, 1, 2, 3, 3, 3, 3, 1, 1, 4]
def baseStart_1964511 : Nat := 118140960795 + 1964511 * 2 ^ 59
def prefixEnd_1964511 : Nat := 4983230072969 + 3 ^ 40 * 1964511 * 2
def baseEnd_1964511 : Nat := 672492262696579050251923

theorem tailTrace_1964511 : CollatzResearch.WordTrace tailWord_1964511 prefixEnd_1964511 672492262696579050251923 := by
  unfold tailWord_1964511
  simp only [CollatzResearch.WordTrace]
  refine ⟨71651602585919633612453387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47767735057279755741635591 71651602585919633612453387)
  ·
    refine ⟨107477403878879450418680081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71651602585919633612453387 107477403878879450418680081)
    ·
      refine ⟨80608052909159587814010061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107477403878879450418680081 80608052909159587814010061)
      ·
        refine ⟨30228019840934845430253773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80608052909159587814010061 30228019840934845430253773)
        ·
          refine ⟨11335507440350567036345165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30228019840934845430253773 11335507440350567036345165)
          ·
            refine ⟨4250815290131462638629437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11335507440350567036345165 4250815290131462638629437)
            ·
              refine ⟨1594055733799298489486039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4250815290131462638629437 1594055733799298489486039)
              ·
                refine ⟨2391083600698947734229059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594055733799298489486039 2391083600698947734229059)
                ·
                  refine ⟨3586625401048421601343589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2391083600698947734229059 3586625401048421601343589)
                  ·
                    refine ⟨672492262696579050251923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3586625401048421601343589 672492262696579050251923)
                    ·
                      rfl

theorem cell22_1964511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 1, 4].length) (baseStart_1964511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964511 prefixEnd_1964511 := by exact prefixLift 1964511
  have htrace : WordTrace (prefixWord ++ tailWord_1964511) baseStart_1964511 baseEnd_1964511 := by
    simpa [prefixWord, tailWord_1964511, baseEnd_1964511] using wordTrace_append hprefix tailTrace_1964511
  have hstable : (prefixWord ++ tailWord_1964511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964511).length < 2 ^ (prefixWord ++ tailWord_1964511).sum := by decide
  have hdescent : baseEnd_1964511 < baseStart_1964511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964526 : List Nat := [4, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_1964526 : Nat := 118140960795 + 1964526 * 2 ^ 59
def prefixEnd_1964526 : Nat := 4983230072969 + 3 ^ 40 * 1964526 * 2
def baseEnd_1964526 : Nat := 224165799167708003708959

theorem tailTrace_1964526 : CollatzResearch.WordTrace tailWord_1964526 prefixEnd_1964526 224165799167708003708959 := by
  unfold tailWord_1964526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8956518710108161396781179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47768099787243527449499621 8956518710108161396781179)
  ·
    refine ⟨13434778065162242095171769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8956518710108161396781179 13434778065162242095171769)
    ·
      refine ⟨10076083548871681571378827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13434778065162242095171769 10076083548871681571378827)
      ·
        refine ⟨15114125323307522357068241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10076083548871681571378827 15114125323307522357068241)
        ·
          refine ⟨11335593992480641767801181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15114125323307522357068241 11335593992480641767801181)
          ·
            refine ⟨4250847747180240662925443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11335593992480641767801181 4250847747180240662925443)
            ·
              refine ⟨6376271620770360994388165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4250847747180240662925443 6376271620770360994388165)
              ·
                refine ⟨1195550928894442686447781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6376271620770360994388165 1195550928894442686447781)
                ·
                  refine ⟨224165799167708003708959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1195550928894442686447781 224165799167708003708959)
                  ·
                    rfl

theorem cell22_1964526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_1964526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964526 prefixEnd_1964526 := by exact prefixLift 1964526
  have htrace : WordTrace (prefixWord ++ tailWord_1964526) baseStart_1964526 baseEnd_1964526 := by
    simpa [prefixWord, tailWord_1964526, baseEnd_1964526] using wordTrace_append hprefix tailTrace_1964526
  have hstable : (prefixWord ++ tailWord_1964526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964526).length < 2 ^ (prefixWord ++ tailWord_1964526).sum := by decide
  have hdescent : baseEnd_1964526 < baseStart_1964526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964537 : List Nat := [1, 2, 1, 3, 1, 2, 5, 7]
def baseStart_1964537 : Nat := 118140960795 + 1964537 * 2 ^ 59
def prefixEnd_1964537 : Nat := 4983230072969 + 3 ^ 40 * 1964537 * 2
def baseEnd_1964537 : Nat := 74722351447547072122427

theorem tailTrace_1964537 : CollatzResearch.WordTrace tailWord_1964537 prefixEnd_1964537 74722351447547072122427 := by
  unfold tailWord_1964537
  simp only [CollatzResearch.WordTrace]
  refine ⟨71652550883825440052899865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47768367255883626701933243 71652550883825440052899865)
  ·
    refine ⟨53739413162869080039674899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71652550883825440052899865 53739413162869080039674899)
    ·
      refine ⟨80609119744303620059512349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53739413162869080039674899 80609119744303620059512349)
      ·
        refine ⟨30228419904113857522317131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80609119744303620059512349 30228419904113857522317131)
        ·
          refine ⟨45342629856170786283475697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30228419904113857522317131 45342629856170786283475697)
          ·
            refine ⟨34006972392128089712606773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45342629856170786283475697 34006972392128089712606773)
            ·
              refine ⟨3188153661762008410556885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34006972392128089712606773 3188153661762008410556885)
              ·
                refine ⟨74722351447547072122427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3188153661762008410556885 74722351447547072122427)
                ·
                  rfl

theorem cell22_1964537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 7].length) (baseStart_1964537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964537 prefixEnd_1964537 := by exact prefixLift 1964537
  have htrace : WordTrace (prefixWord ++ tailWord_1964537) baseStart_1964537 baseEnd_1964537 := by
    simpa [prefixWord, tailWord_1964537, baseEnd_1964537] using wordTrace_append hprefix tailTrace_1964537
  have hstable : (prefixWord ++ tailWord_1964537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964537).length < 2 ^ (prefixWord ++ tailWord_1964537).sum := by decide
  have hdescent : baseEnd_1964537 < baseStart_1964537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964554 : List Nat := [3, 1, 2, 2, 2, 1, 5, 6]
def baseStart_1964554 : Nat := 118140960795 + 1964554 * 2 ^ 59
def prefixEnd_1964554 : Nat := 4983230072969 + 3 ^ 40 * 1964554 * 2
def baseEnd_1964554 : Nat := 74722998052815696825199

theorem tailTrace_1964554 : CollatzResearch.WordTrace tailWord_1964554 prefixEnd_1964554 74722998052815696825199 := by
  unfold tailWord_1964554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17913292731190962989067179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47768780616509234637512477 17913292731190962989067179)
  ·
    refine ⟨26869939096786444483600769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17913292731190962989067179 26869939096786444483600769)
    ·
      refine ⟨20152454322589833362700577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26869939096786444483600769 20152454322589833362700577)
      ·
        refine ⟨15114340741942375022025433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20152454322589833362700577 15114340741942375022025433)
        ·
          refine ⟨11335755556456781266519075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15114340741942375022025433 11335755556456781266519075)
          ·
            refine ⟨17003633334685171899778613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11335755556456781266519075 17003633334685171899778613)
            ·
              refine ⟨1594090625126734865604245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17003633334685171899778613 1594090625126734865604245)
              ·
                refine ⟨74722998052815696825199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1594090625126734865604245 74722998052815696825199)
                ·
                  rfl

theorem cell22_1964554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 6].length) (baseStart_1964554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964554 prefixEnd_1964554 := by exact prefixLift 1964554
  have htrace : WordTrace (prefixWord ++ tailWord_1964554) baseStart_1964554 baseEnd_1964554 := by
    simpa [prefixWord, tailWord_1964554, baseEnd_1964554] using wordTrace_append hprefix tailTrace_1964554
  have hstable : (prefixWord ++ tailWord_1964554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964554).length < 2 ^ (prefixWord ++ tailWord_1964554).sum := by decide
  have hdescent : baseEnd_1964554 < baseStart_1964554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964556 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 2, 4]
def baseStart_1964556 : Nat := 118140960795 + 1964556 * 2 ^ 59
def prefixEnd_1964556 : Nat := 4983230072969 + 3 ^ 40 * 1964556 * 2
def baseEnd_1964556 : Nat := 672507667116213932876785

theorem tailTrace_1964556 : CollatzResearch.WordTrace tailWord_1964556 prefixEnd_1964556 672507667116213932876785 := by
  unfold tailWord_1964556
  simp only [CollatzResearch.WordTrace]
  refine ⟨35826621935378303148920761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47768829247171070865227681 35826621935378303148920761)
  ·
    refine ⟨26869966451533727361690571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35826621935378303148920761 26869966451533727361690571)
    ·
      refine ⟨40304949677300591042535857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26869966451533727361690571 40304949677300591042535857)
      ·
        refine ⟨30228712257975443281901893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40304949677300591042535857 30228712257975443281901893)
        ·
          refine ⟨5667883548370395615356605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30228712257975443281901893 5667883548370395615356605)
          ·
            refine ⟨2125456330638898355758727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5667883548370395615356605 2125456330638898355758727)
            ·
              refine ⟨3188184495958347533638091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2125456330638898355758727 3188184495958347533638091)
              ·
                refine ⟨4782276743937521300457137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3188184495958347533638091 4782276743937521300457137)
                ·
                  refine ⟨3586707557953140975342853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4782276743937521300457137 3586707557953140975342853)
                  ·
                    refine ⟨672507667116213932876785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3586707557953140975342853 672507667116213932876785)
                    ·
                      rfl

theorem cell22_1964556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_1964556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964556 prefixEnd_1964556 := by exact prefixLift 1964556
  have htrace : WordTrace (prefixWord ++ tailWord_1964556) baseStart_1964556 baseEnd_1964556 := by
    simpa [prefixWord, tailWord_1964556, baseEnd_1964556] using wordTrace_append hprefix tailTrace_1964556
  have hstable : (prefixWord ++ tailWord_1964556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964556).length < 2 ^ (prefixWord ++ tailWord_1964556).sum := by decide
  have hdescent : baseEnd_1964556 < baseStart_1964556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964586 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1964586 : Nat := 118140960795 + 1964586 * 2 ^ 59
def prefixEnd_1964586 : Nat := 4983230072969 + 3 ^ 40 * 1964586 * 2
def baseEnd_1964586 : Nat := 672517936729303854626693

theorem tailTrace_1964586 : CollatzResearch.WordTrace tailWord_1964586 prefixEnd_1964586 672517936729303854626693 := by
  unfold tailWord_1964586
  simp only [CollatzResearch.WordTrace]
  refine ⟨17913584515161980355358403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47769558707098614280955741 17913584515161980355358403)
  ·
    refine ⟨26870376772742970533037605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17913584515161980355358403 26870376772742970533037605)
    ·
      refine ⟨5038195644889306974944551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26870376772742970533037605 5038195644889306974944551)
      ·
        refine ⟨7557293467333960462416827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5038195644889306974944551 7557293467333960462416827)
        ·
          refine ⟨11335940201000940693625241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7557293467333960462416827 11335940201000940693625241)
          ·
            refine ⟨8501955150750705520218931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11335940201000940693625241 8501955150750705520218931)
            ·
              refine ⟨12752932726126058280328397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8501955150750705520218931 12752932726126058280328397)
              ·
                refine ⟨4782349772297271855123149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12752932726126058280328397 4782349772297271855123149)
                ·
                  refine ⟨1793381164611476945671181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4782349772297271855123149 1793381164611476945671181)
                  ·
                    refine ⟨672517936729303854626693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1793381164611476945671181 672517936729303854626693)
                    ·
                      rfl

theorem cell22_1964586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1964586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964586 prefixEnd_1964586 := by exact prefixLift 1964586
  have htrace : WordTrace (prefixWord ++ tailWord_1964586) baseStart_1964586 baseEnd_1964586 := by
    simpa [prefixWord, tailWord_1964586, baseEnd_1964586] using wordTrace_append hprefix tailTrace_1964586
  have hstable : (prefixWord ++ tailWord_1964586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964586).length < 2 ^ (prefixWord ++ tailWord_1964586).sum := by decide
  have hdescent : baseEnd_1964586 < baseStart_1964586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964659 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 6, 3]
def baseStart_1964659 : Nat := 118140960795 + 1964659 * 2 ^ 59
def prefixEnd_1964659 : Nat := 4983230072969 + 3 ^ 40 * 1964659 * 2
def baseEnd_1964659 : Nat := 672542926121155997551469

theorem tailTrace_1964659 : CollatzResearch.WordTrace tailWord_1964659 prefixEnd_1964659 672542926121155997551469 := by
  unfold tailWord_1964659
  simp only [CollatzResearch.WordTrace]
  refine ⟨71657000589383454888841031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47771333726255636592560687 71657000589383454888841031)
  ·
    refine ⟨107485500884075182333261547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71657000589383454888841031 107485500884075182333261547)
    ·
      refine ⟨161228251326112773499892321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107485500884075182333261547 161228251326112773499892321)
      ·
        refine ⟨120921188494584580124919241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161228251326112773499892321 120921188494584580124919241)
        ·
          refine ⟨90690891370938435093689431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120921188494584580124919241 90690891370938435093689431)
          ·
            refine ⟨136036337056407652640534147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90690891370938435093689431 136036337056407652640534147)
            ·
              refine ⟨204054505584611478960801221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136036337056407652640534147 204054505584611478960801221)
              ·
                refine ⟨38260219797114652305150229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 204054505584611478960801221 38260219797114652305150229)
                ·
                  refine ⟨1793447802989749326803917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38260219797114652305150229 1793447802989749326803917)
                  ·
                    refine ⟨672542926121155997551469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1793447802989749326803917 672542926121155997551469)
                    ·
                      rfl

theorem cell22_1964659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 3].length) (baseStart_1964659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964659 prefixEnd_1964659 := by exact prefixLift 1964659
  have htrace : WordTrace (prefixWord ++ tailWord_1964659) baseStart_1964659 baseEnd_1964659 := by
    simpa [prefixWord, tailWord_1964659, baseEnd_1964659] using wordTrace_append hprefix tailTrace_1964659
  have hstable : (prefixWord ++ tailWord_1964659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964659).length < 2 ^ (prefixWord ++ tailWord_1964659).sum := by decide
  have hdescent : baseEnd_1964659 < baseStart_1964659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964676 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_1964676 : Nat := 118140960795 + 1964676 * 2 ^ 59
def prefixEnd_1964676 : Nat := 4983230072969 + 3 ^ 40 * 1964676 * 2
def baseEnd_1964676 : Nat := 672548745568573619876417

theorem tailTrace_1964676 : CollatzResearch.WordTrace tailWord_1964676 prefixEnd_1964676 672548745568573619876417 := by
  unfold tailWord_1964676
  simp only [CollatzResearch.WordTrace]
  refine ⟨35828810315160933396104941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47771747086881244528139921 35828810315160933396104941)
  ·
    refine ⟨13435803868185350023539353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35828810315160933396104941 13435803868185350023539353)
    ·
      refine ⟨10076852901139012517654515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13435803868185350023539353 10076852901139012517654515)
      ·
        refine ⟨15115279351708518776481773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10076852901139012517654515 15115279351708518776481773)
        ·
          refine ⟨5668229756890694541180665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15115279351708518776481773 5668229756890694541180665)
          ·
            refine ⟨4251172317668020905885499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5668229756890694541180665 4251172317668020905885499)
            ·
              refine ⟨6376758476502031358828249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4251172317668020905885499 6376758476502031358828249)
              ·
                refine ⟨4782568857376523519121187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6376758476502031358828249 4782568857376523519121187)
                ·
                  refine ⟨7173853286064785278681781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4782568857376523519121187 7173853286064785278681781)
                  ·
                    refine ⟨672548745568573619876417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7173853286064785278681781 672548745568573619876417)
                    ·
                      rfl

theorem cell22_1964676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_1964676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964676 prefixEnd_1964676 := by exact prefixLift 1964676
  have htrace : WordTrace (prefixWord ++ tailWord_1964676) baseStart_1964676 baseEnd_1964676 := by
    simpa [prefixWord, tailWord_1964676, baseEnd_1964676] using wordTrace_append hprefix tailTrace_1964676
  have hstable : (prefixWord ++ tailWord_1964676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964676).length < 2 ^ (prefixWord ++ tailWord_1964676).sum := by decide
  have hdescent : baseEnd_1964676 < baseStart_1964676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964826 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_1964826 : Nat := 118140960795 + 1964826 * 2 ^ 59
def prefixEnd_1964826 : Nat := 4983230072969 + 3 ^ 40 * 1964826 * 2
def baseEnd_1964826 : Nat := 672600093634023228625957

theorem tailTrace_1964826 : CollatzResearch.WordTrace tailWord_1964826 prefixEnd_1964826 672600093634023228625957 := by
  unfold tailWord_1964826
  simp only [CollatzResearch.WordTrace]
  refine ⟨17915772894944610602542583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47775394386518961606780221 17915772894944610602542583)
  ·
    refine ⟨26873659342416915903813875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17915772894944610602542583 26873659342416915903813875)
    ·
      refine ⟨40310489013625373855720813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26873659342416915903813875 40310489013625373855720813)
      ·
        refine ⟨15116433380109515195895305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40310489013625373855720813 15116433380109515195895305)
        ·
          refine ⟨11337325035082136396921479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15116433380109515195895305 11337325035082136396921479)
          ·
            refine ⟨17005987552623204595382219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11337325035082136396921479 17005987552623204595382219)
            ·
              refine ⟨25508981328934806893073329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17005987552623204595382219 25508981328934806893073329)
              ·
                refine ⟨19131735996701105169804997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25508981328934806893073329 19131735996701105169804997)
                ·
                  refine ⟨3587200499381457219338437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19131735996701105169804997 3587200499381457219338437)
                  ·
                    refine ⟨672600093634023228625957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3587200499381457219338437 672600093634023228625957)
                    ·
                      rfl

theorem cell22_1964826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_1964826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964826 prefixEnd_1964826 := by exact prefixLift 1964826
  have htrace : WordTrace (prefixWord ++ tailWord_1964826) baseStart_1964826 baseEnd_1964826 := by
    simpa [prefixWord, tailWord_1964826, baseEnd_1964826] using wordTrace_append hprefix tailTrace_1964826
  have hstable : (prefixWord ++ tailWord_1964826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964826).length < 2 ^ (prefixWord ++ tailWord_1964826).sum := by decide
  have hdescent : baseEnd_1964826 < baseStart_1964826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964862 : List Nat := [4, 2, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_1964862 : Nat := 118140960795 + 1964862 * 2 ^ 59
def prefixEnd_1964862 : Nat := 4983230072969 + 3 ^ 40 * 1964862 * 2
def baseEnd_1964862 : Nat := 672612417169731134725847

theorem tailTrace_1964862 : CollatzResearch.WordTrace tailWord_1964862 prefixEnd_1964862 672612417169731134725847 := by
  unfold tailWord_1964862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8958050575956002569810105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47776269738432013705653893 8958050575956002569810105)
  ·
    refine ⟨6718537931967001927357579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8958050575956002569810105 6718537931967001927357579)
    ·
      refine ⟨10077806897950502891036369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6718537931967001927357579 10077806897950502891036369)
      ·
        refine ⟨7558355173462877168277277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10077806897950502891036369 7558355173462877168277277)
        ·
          refine ⟨2834383190048578938103979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7558355173462877168277277 2834383190048578938103979)
          ·
            refine ⟨4251574785072868407155969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2834383190048578938103979 4251574785072868407155969)
            ·
              refine ⟨3188681088804651305366977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4251574785072868407155969 3188681088804651305366977)
              ·
                refine ⟨2391510816603488479025233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3188681088804651305366977 2391510816603488479025233)
                ·
                  refine ⟨1793633112452616359268925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2391510816603488479025233 1793633112452616359268925)
                  ·
                    refine ⟨672612417169731134725847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1793633112452616359268925 672612417169731134725847)
                    ·
                      rfl

theorem cell22_1964862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_1964862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964862 prefixEnd_1964862 := by exact prefixLift 1964862
  have htrace : WordTrace (prefixWord ++ tailWord_1964862) baseStart_1964862 baseEnd_1964862 := by
    simpa [prefixWord, tailWord_1964862, baseEnd_1964862] using wordTrace_append hprefix tailTrace_1964862
  have hstable : (prefixWord ++ tailWord_1964862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964862).length < 2 ^ (prefixWord ++ tailWord_1964862).sum := by decide
  have hdescent : baseEnd_1964862 < baseStart_1964862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964948 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 6]
def baseStart_1964948 : Nat := 118140960795 + 1964948 * 2 ^ 59
def prefixEnd_1964948 : Nat := 4983230072969 + 3 ^ 40 * 1964948 * 2
def baseEnd_1964948 : Nat := 224213952242418525691861

theorem tailTrace_1964948 : CollatzResearch.WordTrace tailWord_1964948 prefixEnd_1964948 224213952242418525691861 := by
  unfold tailWord_1964948
  simp only [CollatzResearch.WordTrace]
  refine ⟨35833770642668228623055749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47778360856890971497407665 35833770642668228623055749)
  ·
    refine ⟨6718831995500292866822953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35833770642668228623055749 6718831995500292866822953)
    ·
      refine ⟨5039123996625219650117215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6718831995500292866822953 5039123996625219650117215)
      ·
        refine ⟨7558685994937829475175823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5039123996625219650117215 7558685994937829475175823)
        ·
          refine ⟨11338028992406744212763735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7558685994937829475175823 11338028992406744212763735)
          ·
            refine ⟨17007043488610116319145603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11338028992406744212763735 17007043488610116319145603)
            ·
              refine ⟨25510565232915174478718405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17007043488610116319145603 25510565232915174478718405)
              ·
                refine ⟨4783230981171595214759701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25510565232915174478718405 4783230981171595214759701)
                ·
                  refine ⟨224213952242418525691861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4783230981171595214759701 224213952242418525691861)
                  ·
                    rfl

theorem cell22_1964948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_1964948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964948 prefixEnd_1964948 := by exact prefixLift 1964948
  have htrace : WordTrace (prefixWord ++ tailWord_1964948) baseStart_1964948 baseEnd_1964948 := by
    simpa [prefixWord, tailWord_1964948, baseEnd_1964948] using wordTrace_append hprefix tailTrace_1964948
  have hstable : (prefixWord ++ tailWord_1964948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964948).length < 2 ^ (prefixWord ++ tailWord_1964948).sum := by decide
  have hdescent : baseEnd_1964948 < baseStart_1964948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964963 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 4, 3]
def baseStart_1964963 : Nat := 118140960795 + 1964963 * 2 ^ 59
def prefixEnd_1964963 : Nat := 4983230072969 + 3 ^ 40 * 1964963 * 2
def baseEnd_1964963 : Nat := 672646991533800537950537

theorem tailTrace_1964963 : CollatzResearch.WordTrace tailWord_1964963 prefixEnd_1964963 672646991533800537950537 := by
  unfold tailWord_1964963
  simp only [CollatzResearch.WordTrace]
  refine ⟨71668088380282114807907543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47778725586854743205271695 71668088380282114807907543)
  ·
    refine ⟨107502132570423172211861315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71668088380282114807907543 107502132570423172211861315)
    ·
      refine ⟨161253198855634758317791973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107502132570423172211861315 161253198855634758317791973)
      ·
        refine ⟨30234974785431517184585995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161253198855634758317791973 30234974785431517184585995)
        ·
          refine ⟨45352462178147275776878993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30234974785431517184585995 45352462178147275776878993)
          ·
            refine ⟨34014346633610456832659245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45352462178147275776878993 34014346633610456832659245)
            ·
              refine ⟨12755379987603921312247217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34014346633610456832659245 12755379987603921312247217)
              ·
                refine ⟨9566534990702940984185413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12755379987603921312247217 9566534990702940984185413)
                ·
                  refine ⟨1793725310756801434534765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9566534990702940984185413 1793725310756801434534765)
                  ·
                    refine ⟨672646991533800537950537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1793725310756801434534765 672646991533800537950537)
                    ·
                      rfl

theorem cell22_1964963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 3].length) (baseStart_1964963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964963 prefixEnd_1964963 := by exact prefixLift 1964963
  have htrace : WordTrace (prefixWord ++ tailWord_1964963) baseStart_1964963 baseEnd_1964963 := by
    simpa [prefixWord, tailWord_1964963, baseEnd_1964963] using wordTrace_append hprefix tailTrace_1964963
  have hstable : (prefixWord ++ tailWord_1964963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964963).length < 2 ^ (prefixWord ++ tailWord_1964963).sum := by decide
  have hdescent : baseEnd_1964963 < baseStart_1964963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1964991 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 2, 7]
def baseStart_1964991 : Nat := 118140960795 + 1964991 * 2 ^ 59
def prefixEnd_1964991 : Nat := 4983230072969 + 3 ^ 40 * 1964991 * 2
def baseEnd_1964991 : Nat := 672656576506017798250451

theorem tailTrace_1964991 : CollatzResearch.WordTrace tailWord_1964991 prefixEnd_1964991 672656576506017798250451 := by
  unfold tailWord_1964991
  simp only [CollatzResearch.WordTrace]
  refine ⟨71669109624180675589926827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47779406416120450393284551 71669109624180675589926827)
  ·
    refine ⟨107503664436271013384890241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71669109624180675589926827 107503664436271013384890241)
    ·
      refine ⟨80627748327203260038667681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107503664436271013384890241 80627748327203260038667681)
      ·
        refine ⟨60470811245402445029000761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80627748327203260038667681 60470811245402445029000761)
        ·
          refine ⟨45353108434051833771750571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60470811245402445029000761 45353108434051833771750571)
          ·
            refine ⟨68029662651077750657625857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45353108434051833771750571 68029662651077750657625857)
            ·
              refine ⟨51022246988308312993219393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68029662651077750657625857 51022246988308312993219393)
              ·
                refine ⟨38266685241231234744914545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51022246988308312993219393 38266685241231234744914545)
                ·
                  refine ⟨28700013930923426058685909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38266685241231234744914545 28700013930923426058685909)
                  ·
                    refine ⟨672656576506017798250451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28700013930923426058685909 672656576506017798250451)
                    ·
                      rfl

theorem cell22_1964991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_1964991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1964991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1964991 prefixEnd_1964991 := by exact prefixLift 1964991
  have htrace : WordTrace (prefixWord ++ tailWord_1964991) baseStart_1964991 baseEnd_1964991 := by
    simpa [prefixWord, tailWord_1964991, baseEnd_1964991] using wordTrace_append hprefix tailTrace_1964991
  have hstable : (prefixWord ++ tailWord_1964991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1964991).length < 2 ^ (prefixWord ++ tailWord_1964991).sum := by decide
  have hdescent : baseEnd_1964991 < baseStart_1964991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1964991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965008 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 5, 3]
def baseStart_1965008 : Nat := 118140960795 + 1965008 * 2 ^ 59
def prefixEnd_1965008 : Nat := 4983230072969 + 3 ^ 40 * 1965008 * 2
def baseEnd_1965008 : Nat := 672662395953435420575399

theorem tailTrace_1965008 : CollatzResearch.WordTrace tailWord_1965008 prefixEnd_1965008 672662395953435420575399 := by
  unfold tailWord_1965008
  simp only [CollatzResearch.WordTrace]
  refine ⟨35834864832559543746647839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47779819776746058328863785 35834864832559543746647839)
  ·
    refine ⟨53752297248839315619971759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35834864832559543746647839 53752297248839315619971759)
    ·
      refine ⟨80628445873258973429957639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53752297248839315619971759 80628445873258973429957639)
      ·
        refine ⟨120942668809888460144936459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80628445873258973429957639 120942668809888460144936459)
        ·
          refine ⟨181414003214832690217404689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120942668809888460144936459 181414003214832690217404689)
          ·
            refine ⟨136060502411124517663053517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181414003214832690217404689 136060502411124517663053517)
            ·
              refine ⟨51022688404171694123645069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136060502411124517663053517 51022688404171694123645069)
              ·
                refine ⟨19133508151564385296366901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51022688404171694123645069 19133508151564385296366901)
                ·
                  refine ⟨1793766389209161121534397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19133508151564385296366901 1793766389209161121534397)
                  ·
                    refine ⟨672662395953435420575399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1793766389209161121534397 672662395953435420575399)
                    ·
                      rfl

theorem cell22_1965008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 5, 3].length) (baseStart_1965008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965008 prefixEnd_1965008 := by exact prefixLift 1965008
  have htrace : WordTrace (prefixWord ++ tailWord_1965008) baseStart_1965008 baseEnd_1965008 := by
    simpa [prefixWord, tailWord_1965008, baseEnd_1965008] using wordTrace_append hprefix tailTrace_1965008
  have hstable : (prefixWord ++ tailWord_1965008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965008).length < 2 ^ (prefixWord ++ tailWord_1965008).sum := by decide
  have hdescent : baseEnd_1965008 < baseStart_1965008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965100 : List Nat := [2, 2, 1, 1, 1, 2, 3, 6, 4]
def baseStart_1965100 : Nat := 118140960795 + 1965100 * 2 ^ 59
def prefixEnd_1965100 : Nat := 4983230072969 + 3 ^ 40 * 1965100 * 2
def baseEnd_1965100 : Nat := 224231296477859282425039

theorem tailTrace_1965100 : CollatzResearch.WordTrace tailWord_1965100 prefixEnd_1965100 224231296477859282425039 := by
  unfold tailWord_1965100
  simp only [CollatzResearch.WordTrace]
  refine ⟨35836542590392893602822377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47782056787190524803763169 35836542590392893602822377)
  ·
    refine ⟨26877406942794670202116783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35836542590392893602822377 26877406942794670202116783)
    ·
      refine ⟨40316110414192005303175175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26877406942794670202116783 40316110414192005303175175)
      ·
        refine ⟨60474165621288007954762763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40316110414192005303175175 60474165621288007954762763)
        ·
          refine ⟨90711248431932011932144145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60474165621288007954762763 90711248431932011932144145)
          ·
            refine ⟨68033436323949008949108109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90711248431932011932144145 68033436323949008949108109)
            ·
              refine ⟨25512538621480878355915541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68033436323949008949108109 25512538621480878355915541)
              ·
                refine ⟨1195900247881916172933541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25512538621480878355915541 1195900247881916172933541)
                ·
                  refine ⟨224231296477859282425039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1195900247881916172933541 224231296477859282425039)
                  ·
                    rfl

theorem cell22_1965100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_1965100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965100 prefixEnd_1965100 := by exact prefixLift 1965100
  have htrace : WordTrace (prefixWord ++ tailWord_1965100) baseStart_1965100 baseEnd_1965100 := by
    simpa [prefixWord, tailWord_1965100, baseEnd_1965100] using wordTrace_append hprefix tailTrace_1965100
  have hstable : (prefixWord ++ tailWord_1965100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965100).length < 2 ^ (prefixWord ++ tailWord_1965100).sum := by decide
  have hdescent : baseEnd_1965100 < baseStart_1965100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965128 : List Nat := [2, 1, 3, 1, 1, 1, 5, 8]
def baseStart_1965128 : Nat := 118140960795 + 1965128 * 2 ^ 59
def prefixEnd_1965128 : Nat := 4983230072969 + 3 ^ 40 * 1965128 * 2
def baseEnd_1965128 : Nat := 74744830489532789730559

theorem tailTrace_1965128 : CollatzResearch.WordTrace tailWord_1965128 prefixEnd_1965128 74744830489532789730559 := by
  unfold tailWord_1965128
  simp only [CollatzResearch.WordTrace]
  refine ⟨35837053212342173993832019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47782737616456231991776025 35837053212342173993832019)
  ·
    refine ⟨53755579818513260990748029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35837053212342173993832019 53755579818513260990748029)
    ·
      refine ⟨20158342431942472871530511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53755579818513260990748029 20158342431942472871530511)
      ·
        refine ⟨30237513647913709307295767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20158342431942472871530511 30237513647913709307295767)
        ·
          refine ⟨45356270471870563960943651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30237513647913709307295767 45356270471870563960943651)
          ·
            refine ⟨68034405707805845941415477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45356270471870563960943651 68034405707805845941415477)
            ·
              refine ⟨6378225535106798057007701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68034405707805845941415477 6378225535106798057007701)
              ·
                refine ⟨74744830489532789730559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6378225535106798057007701 74744830489532789730559)
                ·
                  rfl

theorem cell22_1965128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 8].length) (baseStart_1965128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965128 prefixEnd_1965128 := by exact prefixLift 1965128
  have htrace : WordTrace (prefixWord ++ tailWord_1965128) baseStart_1965128 baseEnd_1965128 := by
    simpa [prefixWord, tailWord_1965128, baseEnd_1965128] using wordTrace_append hprefix tailTrace_1965128
  have hstable : (prefixWord ++ tailWord_1965128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965128).length < 2 ^ (prefixWord ++ tailWord_1965128).sum := by decide
  have hdescent : baseEnd_1965128 < baseStart_1965128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965166 : List Nat := [4, 1, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_1965166 : Nat := 118140960795 + 1965166 * 2 ^ 59
def prefixEnd_1965166 : Nat := 4983230072969 + 3 ^ 40 * 1965166 * 2
def baseEnd_1965166 : Nat := 672716482582375675124915

theorem tailTrace_1965166 : CollatzResearch.WordTrace tailWord_1965166 prefixEnd_1965166 672716482582375675124915 := by
  unfold tailWord_1965166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8959436549818335059693419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47783661599031120318364901 8959436549818335059693419)
  ·
    refine ⟨13439154824727502589540129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8959436549818335059693419 13439154824727502589540129)
    ·
      refine ⟨10079366118545626942155097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13439154824727502589540129 10079366118545626942155097)
      ·
        refine ⟨7559524588909220206616323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10079366118545626942155097 7559524588909220206616323)
        ·
          refine ⟨11339286883363830309924485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7559524588909220206616323 11339286883363830309924485)
          ·
            refine ⟨2126116290630718183110841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11339286883363830309924485 2126116290630718183110841)
            ·
              refine ⟨1594587217973038637333131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2126116290630718183110841 1594587217973038637333131)
              ·
                refine ⟨2391880826959557955999697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594587217973038637333131 2391880826959557955999697)
                ·
                  refine ⟨1793910620219668466999773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2391880826959557955999697 1793910620219668466999773)
                  ·
                    refine ⟨672716482582375675124915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1793910620219668466999773 672716482582375675124915)
                    ·
                      rfl

theorem cell22_1965166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_1965166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965166 prefixEnd_1965166 := by exact prefixLift 1965166
  have htrace : WordTrace (prefixWord ++ tailWord_1965166) baseStart_1965166 baseEnd_1965166 := by
    simpa [prefixWord, tailWord_1965166, baseEnd_1965166] using wordTrace_append hprefix tailTrace_1965166
  have hstable : (prefixWord ++ tailWord_1965166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965166).length < 2 ^ (prefixWord ++ tailWord_1965166).sum := by decide
  have hdescent : baseEnd_1965166 < baseStart_1965166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965194 : List Nat := [3, 1, 2, 3, 1, 1, 2, 5, 1, 3]
def baseStart_1965194 : Nat := 118140960795 + 1965194 * 2 ^ 59
def prefixEnd_1965194 : Nat := 4983230072969 + 3 ^ 40 * 1965194 * 2
def baseEnd_1965194 : Nat := 672726067554592935424829

theorem tailTrace_1965194 : CollatzResearch.WordTrace tailWord_1965194 prefixEnd_1965194 672726067554592935424829 := by
  unfold tailWord_1965194
  simp only [CollatzResearch.WordTrace]
  refine ⟨17919128410611310314891659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47784342428296827506377757 17919128410611310314891659)
  ·
    refine ⟨26878692615916965472337489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17919128410611310314891659 26878692615916965472337489)
    ·
      refine ⟨20159019461937724104253117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26878692615916965472337489 20159019461937724104253117)
      ·
        refine ⟨7559632298226646539094919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20159019461937724104253117 7559632298226646539094919)
        ·
          refine ⟨11339448447339969808642379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7559632298226646539094919 11339448447339969808642379)
          ·
            refine ⟨17009172671009954712963569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11339448447339969808642379 17009172671009954712963569)
            ·
              refine ⟨12756879503257466034722677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17009172671009954712963569 12756879503257466034722677)
              ·
                refine ⟨1195957453430387440755251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12756879503257466034722677 1195957453430387440755251)
                ·
                  refine ⟨1793936180145581161132877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1195957453430387440755251 1793936180145581161132877)
                  ·
                    refine ⟨672726067554592935424829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1793936180145581161132877 672726067554592935424829)
                    ·
                      rfl

theorem cell22_1965194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_1965194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965194 prefixEnd_1965194 := by exact prefixLift 1965194
  have htrace : WordTrace (prefixWord ++ tailWord_1965194) baseStart_1965194 baseEnd_1965194 := by
    simpa [prefixWord, tailWord_1965194, baseEnd_1965194] using wordTrace_append hprefix tailTrace_1965194
  have hstable : (prefixWord ++ tailWord_1965194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965194).length < 2 ^ (prefixWord ++ tailWord_1965194).sum := by decide
  have hdescent : baseEnd_1965194 < baseStart_1965194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965207 : List Nat := [1, 1, 3, 3, 3, 2, 2, 2, 5]
def baseStart_1965207 : Nat := 118140960795 + 1965207 * 2 ^ 59
def prefixEnd_1965207 : Nat := 4983230072969 + 3 ^ 40 * 1965207 * 2
def baseEnd_1965207 : Nat := 224243505906755078283263

theorem tailTrace_1965207 : CollatzResearch.WordTrace tailWord_1965207 prefixEnd_1965207 224243505906755078283263 := by
  unfold tailWord_1965207
  simp only [CollatzResearch.WordTrace]
  refine ⟨71676987791398144479789875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47784658527598762986526583 71676987791398144479789875)
  ·
    refine ⟨107515481687097216719684813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71676987791398144479789875 107515481687097216719684813)
    ·
      refine ⟨40318305632661456269881805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107515481687097216719684813 40318305632661456269881805)
      ·
        refine ⟨15119364612248046101205677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40318305632661456269881805 15119364612248046101205677)
        ·
          refine ⟨5669761729593017287952129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15119364612248046101205677 5669761729593017287952129)
          ·
            refine ⟨4252321297194762965964097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5669761729593017287952129 4252321297194762965964097)
            ·
              refine ⟨3189240972896072224473073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4252321297194762965964097 3189240972896072224473073)
              ·
                refine ⟨2391930729672054168354805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3189240972896072224473073 2391930729672054168354805)
                ·
                  refine ⟨224243505906755078283263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2391930729672054168354805 224243505906755078283263)
                  ·
                    rfl

theorem cell22_1965207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 5].length) (baseStart_1965207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965207 prefixEnd_1965207 := by exact prefixLift 1965207
  have htrace : WordTrace (prefixWord ++ tailWord_1965207) baseStart_1965207 baseEnd_1965207 := by
    simpa [prefixWord, tailWord_1965207, baseEnd_1965207] using wordTrace_append hprefix tailTrace_1965207
  have hstable : (prefixWord ++ tailWord_1965207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965207).length < 2 ^ (prefixWord ++ tailWord_1965207).sum := by decide
  have hdescent : baseEnd_1965207 < baseStart_1965207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965265 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 4, 4]
def baseStart_1965265 : Nat := 118140960795 + 1965265 * 2 ^ 59
def prefixEnd_1965265 : Nat := 4983230072969 + 3 ^ 40 * 1965265 * 2
def baseEnd_1965265 : Nat := 672750372305572416899611

theorem tailTrace_1965265 : CollatzResearch.WordTrace tailWord_1965265 prefixEnd_1965265 672750372305572416899611 := by
  unfold tailWord_1965265
  simp only [CollatzResearch.WordTrace]
  refine ⟨71679103225188020385401249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47786068816792013590267499 71679103225188020385401249)
  ·
    refine ⟨53759327418891015289050937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71679103225188020385401249 53759327418891015289050937)
    ·
      refine ⟨40319495564168261466788203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53759327418891015289050937 40319495564168261466788203)
      ·
        refine ⟨60479243346252392200182305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40319495564168261466788203 60479243346252392200182305)
        ·
          refine ⟨45359432509689294150136729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60479243346252392200182305 45359432509689294150136729)
          ·
            refine ⟨34019574382266970612602547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45359432509689294150136729 34019574382266970612602547)
            ·
              refine ⟨51029361573400455918903821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34019574382266970612602547 51029361573400455918903821)
              ·
                refine ⟨19136010590025170969588933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51029361573400455918903821 19136010590025170969588933)
                ·
                  refine ⟨3588001985629719556797925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19136010590025170969588933 3588001985629719556797925)
                  ·
                    refine ⟨672750372305572416899611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3588001985629719556797925 672750372305572416899611)
                    ·
                      rfl

theorem cell22_1965265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_1965265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965265 prefixEnd_1965265 := by exact prefixLift 1965265
  have htrace : WordTrace (prefixWord ++ tailWord_1965265) baseStart_1965265 baseEnd_1965265 := by
    simpa [prefixWord, tailWord_1965265, baseEnd_1965265] using wordTrace_append hprefix tailTrace_1965265
  have hstable : (prefixWord ++ tailWord_1965265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965265).length < 2 ^ (prefixWord ++ tailWord_1965265).sum := by decide
  have hdescent : baseEnd_1965265 < baseStart_1965265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965269 : List Nat := [1, 3, 2, 4, 1, 1, 2, 4, 4]
def baseStart_1965269 : Nat := 118140960795 + 1965269 * 2 ^ 59
def prefixEnd_1965269 : Nat := 4983230072969 + 3 ^ 40 * 1965269 * 2
def baseEnd_1965269 : Nat := 224250580529105913266533

theorem tailTrace_1965269 : CollatzResearch.WordTrace tailWord_1965269 prefixEnd_1965269 224250580529105913266533 := by
  unfold tailWord_1965269
  simp only [CollatzResearch.WordTrace]
  refine ⟨71679249117173529068546861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47786166078115686045697907 71679249117173529068546861)
  ·
    refine ⟨26879718418940073400705073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71679249117173529068546861 26879718418940073400705073)
    ·
      refine ⟨20159788814205055050528805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26879718418940073400705073 20159788814205055050528805)
      ·
        refine ⟨3779960402663447821974151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20159788814205055050528805 3779960402663447821974151)
        ·
          refine ⟨5669940603995171732961227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3779960402663447821974151 5669940603995171732961227)
          ·
            refine ⟨8504910905992757599441841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5669940603995171732961227 8504910905992757599441841)
            ·
              refine ⟨6378683179494568199581381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8504910905992757599441841 6378683179494568199581381)
              ·
                refine ⟨1196003096155231537421509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6378683179494568199581381 1196003096155231537421509)
                ·
                  refine ⟨224250580529105913266533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1196003096155231537421509 224250580529105913266533)
                  ·
                    rfl

theorem cell22_1965269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_1965269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965269 prefixEnd_1965269 := by exact prefixLift 1965269
  have htrace : WordTrace (prefixWord ++ tailWord_1965269) baseStart_1965269 baseEnd_1965269 := by
    simpa [prefixWord, tailWord_1965269, baseEnd_1965269] using wordTrace_append hprefix tailTrace_1965269
  have hstable : (prefixWord ++ tailWord_1965269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965269).length < 2 ^ (prefixWord ++ tailWord_1965269).sum := by decide
  have hdescent : baseEnd_1965269 < baseStart_1965269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965314 : List Nat := [3, 4, 1, 1, 3, 2, 8]
def baseStart_1965314 : Nat := 118140960795 + 1965314 * 2 ^ 59
def prefixEnd_1965314 : Nat := 4983230072969 + 3 ^ 40 * 1965314 * 2
def baseEnd_1965314 : Nat := 24917301703961208237943

theorem tailTrace_1965314 : CollatzResearch.WordTrace tailWord_1965314 prefixEnd_1965314 24917301703961208237943 := by
  unfold tailWord_1965314
  simp only [CollatzResearch.WordTrace]
  refine ⟨17920222600502625438483749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47787260268007001169289997 17920222600502625438483749)
  ·
    refine ⟨3360041737594242269715703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17920222600502625438483749 3360041737594242269715703)
    ·
      refine ⟨5040062606391363404573555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3360041737594242269715703 5040062606391363404573555)
      ·
        refine ⟨7560093909587045106860333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5040062606391363404573555 7560093909587045106860333)
        ·
          refine ⟨2835035216095141915072625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7560093909587045106860333 2835035216095141915072625)
          ·
            refine ⟨2126276412071356436304469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2835035216095141915072625 2126276412071356436304469)
            ·
              refine ⟨24917301703961208237943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2126276412071356436304469 24917301703961208237943)
              ·
                rfl

theorem cell22_1965314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 8].length) (baseStart_1965314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965314 prefixEnd_1965314 := by exact prefixLift 1965314
  have htrace : WordTrace (prefixWord ++ tailWord_1965314) baseStart_1965314 baseEnd_1965314 := by
    simpa [prefixWord, tailWord_1965314, baseEnd_1965314] using wordTrace_append hprefix tailTrace_1965314
  have hstable : (prefixWord ++ tailWord_1965314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965314).length < 2 ^ (prefixWord ++ tailWord_1965314).sum := by decide
  have hdescent : baseEnd_1965314 < baseStart_1965314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965380 : List Nat := [2, 3, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1965380 : Nat := 118140960795 + 1965380 * 2 ^ 59
def prefixEnd_1965380 : Nat := 4983230072969 + 3 ^ 40 * 1965380 * 2
def baseEnd_1965380 : Nat := 672789739155750450274259

theorem tailTrace_1965380 : CollatzResearch.WordTrace tailWord_1965380 prefixEnd_1965380 672789739155750450274259 := by
  unfold tailWord_1965380
  simp only [CollatzResearch.WordTrace]
  refine ⟨35841648809885697512918797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47788865079847596683891729 35841648809885697512918797)
  ·
    refine ⟨13440618303707136567344549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35841648809885697512918797 13440618303707136567344549)
    ·
      refine ⟨2520115931945088106377103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13440618303707136567344549 2520115931945088106377103)
      ·
        refine ⟨3780173897917632159565655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2520115931945088106377103 3780173897917632159565655)
        ·
          refine ⟨5670260846876448239348483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3780173897917632159565655 5670260846876448239348483)
          ·
            refine ⟨8505391270314672359022725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5670260846876448239348483 8505391270314672359022725)
            ·
              refine ⟨1594760863184001067316761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8505391270314672359022725 1594760863184001067316761)
              ·
                refine ⟨1196070647388000800487571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1594760863184001067316761 1196070647388000800487571)
                ·
                  refine ⟨1794105971082001200731357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196070647388000800487571 1794105971082001200731357)
                  ·
                    refine ⟨672789739155750450274259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1794105971082001200731357 672789739155750450274259)
                    ·
                      rfl

theorem cell22_1965380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1965380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965380 prefixEnd_1965380 := by exact prefixLift 1965380
  have htrace : WordTrace (prefixWord ++ tailWord_1965380) baseStart_1965380 baseEnd_1965380 := by
    simpa [prefixWord, tailWord_1965380, baseEnd_1965380] using wordTrace_append hprefix tailTrace_1965380
  have hstable : (prefixWord ++ tailWord_1965380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965380).length < 2 ^ (prefixWord ++ tailWord_1965380).sum := by decide
  have hdescent : baseEnd_1965380 < baseStart_1965380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965402 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_1965402 : Nat := 118140960795 + 1965402 * 2 ^ 59
def prefixEnd_1965402 : Nat := 4983230072969 + 3 ^ 40 * 1965402 * 2
def baseEnd_1965402 : Nat := 672797270205349726224191

theorem tailTrace_1965402 : CollatzResearch.WordTrace tailWord_1965402 prefixEnd_1965402 672797270205349726224191 := by
  unfold tailWord_1965402
  simp only [CollatzResearch.WordTrace]
  refine ⟨17921025006422923195784615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47789400017127795188758973 17921025006422923195784615)
  ·
    refine ⟨26881537509634384793676923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17921025006422923195784615 26881537509634384793676923)
    ·
      refine ⟨40322306264451577190515385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26881537509634384793676923 40322306264451577190515385)
      ·
        refine ⟨30241729698338682892886539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40322306264451577190515385 30241729698338682892886539)
        ·
          refine ⟨45362594547508024339329809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30241729698338682892886539 45362594547508024339329809)
          ·
            refine ⟨34021945910631018254497357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45362594547508024339329809 34021945910631018254497357)
            ·
              refine ⟨12758229716486631845436509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34021945910631018254497357 12758229716486631845436509)
              ·
                refine ⟨4784336143682486942038691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12758229716486631845436509 4784336143682486942038691)
                ·
                  refine ⟨7176504215523730413058037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4784336143682486942038691 7176504215523730413058037)
                  ·
                    refine ⟨672797270205349726224191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7176504215523730413058037 672797270205349726224191)
                    ·
                      rfl

theorem cell22_1965402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_1965402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965402 prefixEnd_1965402 := by exact prefixLift 1965402
  have htrace : WordTrace (prefixWord ++ tailWord_1965402) baseStart_1965402 baseEnd_1965402 := by
    simpa [prefixWord, tailWord_1965402, baseEnd_1965402] using wordTrace_append hprefix tailTrace_1965402
  have hstable : (prefixWord ++ tailWord_1965402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965402).length < 2 ^ (prefixWord ++ tailWord_1965402).sum := by decide
  have hdescent : baseEnd_1965402 < baseStart_1965402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965417 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 2, 4]
def baseStart_1965417 : Nat := 118140960795 + 1965417 * 2 ^ 59
def prefixEnd_1965417 : Nat := 4983230072969 + 3 ^ 40 * 1965417 * 2
def baseEnd_1965417 : Nat := 672802405011894687099145

theorem tailTrace_1965417 : CollatzResearch.WordTrace tailWord_1965417 prefixEnd_1965417 672802405011894687099145 := by
  unfold tailWord_1965417
  simp only [CollatzResearch.WordTrace]
  refine ⟨71684647120637350344934505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47789764747091566896623003 71684647120637350344934505)
  ·
    refine ⟨53763485340478012758700879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71684647120637350344934505 53763485340478012758700879)
    ·
      refine ⟨80645228010717019138051319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53763485340478012758700879 80645228010717019138051319)
      ·
        refine ⟨120967842016075528707076979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80645228010717019138051319 120967842016075528707076979)
        ·
          refine ⟨181451763024113293060615469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120967842016075528707076979 181451763024113293060615469)
          ·
            refine ⟨68044411134042484897730801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181451763024113293060615469 68044411134042484897730801)
            ·
              refine ⟨51033308350531863673298101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68044411134042484897730801 51033308350531863673298101)
              ·
                refine ⟨4784372657862362219371697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51033308350531863673298101 4784372657862362219371697)
                ·
                  refine ⟨3588279493396771664528773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4784372657862362219371697 3588279493396771664528773)
                  ·
                    refine ⟨672802405011894687099145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3588279493396771664528773 672802405011894687099145)
                    ·
                      rfl

theorem cell22_1965417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_1965417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965417 prefixEnd_1965417 := by exact prefixLift 1965417
  have htrace : WordTrace (prefixWord ++ tailWord_1965417) baseStart_1965417 baseEnd_1965417 := by
    simpa [prefixWord, tailWord_1965417, baseEnd_1965417] using wordTrace_append hprefix tailTrace_1965417
  have hstable : (prefixWord ++ tailWord_1965417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965417).length < 2 ^ (prefixWord ++ tailWord_1965417).sum := by decide
  have hdescent : baseEnd_1965417 < baseStart_1965417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965421 : List Nat := [1, 5, 1, 1, 1, 4, 2, 3, 4]
def baseStart_1965421 : Nat := 118140960795 + 1965421 * 2 ^ 59
def prefixEnd_1965421 : Nat := 4983230072969 + 3 ^ 40 * 1965421 * 2
def baseEnd_1965421 : Nat := 224267924764546669999711

theorem tailTrace_1965421 : CollatzResearch.WordTrace tailWord_1965421 prefixEnd_1965421 224267924764546669999711 := by
  unfold tailWord_1965421
  simp only [CollatzResearch.WordTrace]
  refine ⟨71684793012622859028080117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47789862008415239352053411 71684793012622859028080117)
  ·
    refine ⟨6720449344933393033882511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71684793012622859028080117 6720449344933393033882511)
    ·
      refine ⟨10080674017400089550823767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6720449344933393033882511 10080674017400089550823767)
      ·
        refine ⟨15121011026100134326235651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10080674017400089550823767 15121011026100134326235651)
        ·
          refine ⟨22681516539150201489353477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15121011026100134326235651 22681516539150201489353477)
          ·
            refine ⟨4252784351090662779253777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22681516539150201489353477 4252784351090662779253777)
            ·
              refine ⟨3189588263317997084440333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4252784351090662779253777 3189588263317997084440333)
              ·
                refine ⟨1196095598744248906665125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3189588263317997084440333 1196095598744248906665125)
                ·
                  refine ⟨224267924764546669999711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1196095598744248906665125 224267924764546669999711)
                  ·
                    rfl

theorem cell22_1965421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_1965421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965421 prefixEnd_1965421 := by exact prefixLift 1965421
  have htrace : WordTrace (prefixWord ++ tailWord_1965421) baseStart_1965421 baseEnd_1965421 := by
    simpa [prefixWord, tailWord_1965421, baseEnd_1965421] using wordTrace_append hprefix tailTrace_1965421
  have hstable : (prefixWord ++ tailWord_1965421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965421).length < 2 ^ (prefixWord ++ tailWord_1965421).sum := by decide
  have hdescent : baseEnd_1965421 < baseStart_1965421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965438 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_1965438 : Nat := 118140960795 + 1965438 * 2 ^ 59
def prefixEnd_1965438 : Nat := 4983230072969 + 3 ^ 40 * 1965438 * 2
def baseEnd_1965438 : Nat := 224269864580352544108027

theorem tailTrace_1965438 : CollatzResearch.WordTrace tailWord_1965438 prefixEnd_1965438 224269864580352544108027 := by
  unfold tailWord_1965438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8960676631695158866431121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47790275369040847287632645 8960676631695158866431121)
  ·
    refine ⟨6720507473771369149823341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8960676631695158866431121 6720507473771369149823341)
    ·
      refine ⟨2520190302664263431183753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6720507473771369149823341 2520190302664263431183753)
      ·
        refine ⟨1890142726998197573387815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2520190302664263431183753 1890142726998197573387815)
        ·
          refine ⟨2835214090497296360081723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890142726998197573387815 2835214090497296360081723)
          ·
            refine ⟨4252821135745944540122585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835214090497296360081723 4252821135745944540122585)
            ·
              refine ⟨3189615851809458405091939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4252821135745944540122585 3189615851809458405091939)
              ·
                refine ⟨4784423777714187607637909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3189615851809458405091939 4784423777714187607637909)
                ·
                  refine ⟨224269864580352544108027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4784423777714187607637909 224269864580352544108027)
                  ·
                    rfl

theorem cell22_1965438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_1965438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965438 prefixEnd_1965438 := by exact prefixLift 1965438
  have htrace : WordTrace (prefixWord ++ tailWord_1965438) baseStart_1965438 baseEnd_1965438 := by
    simpa [prefixWord, tailWord_1965438, baseEnd_1965438] using wordTrace_append hprefix tailTrace_1965438
  have hstable : (prefixWord ++ tailWord_1965438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965438).length < 2 ^ (prefixWord ++ tailWord_1965438).sum := by decide
  have hdescent : baseEnd_1965438 < baseStart_1965438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965549 : List Nat := [1, 5, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_1965549 : Nat := 118140960795 + 1965549 * 2 ^ 59
def prefixEnd_1965549 : Nat := 4983230072969 + 3 ^ 40 * 1965549 * 2
def baseEnd_1965549 : Nat := 672847591309490342798741

theorem tailTrace_1965549 : CollatzResearch.WordTrace tailWord_1965549 prefixEnd_1965549 672847591309490342798741 := by
  unfold tailWord_1965549
  simp only [CollatzResearch.WordTrace]
  refine ⟨71689461556159136888739701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47792974370772757925826467 71689461556159136888739701)
  ·
    refine ⟨6720887020889919083319347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71689461556159136888739701 6720887020889919083319347)
    ·
      refine ⟨10081330531334878624979021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6720887020889919083319347 10081330531334878624979021)
      ·
        refine ⟨3780498949250579484367133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10081330531334878624979021 3780498949250579484367133)
        ·
          refine ⟨1417687105968967306637675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3780498949250579484367133 1417687105968967306637675)
          ·
            refine ⟨2126530658953450959956513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1417687105968967306637675 2126530658953450959956513)
            ·
              refine ⟨1594897994215088219967385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2126530658953450959956513 1594897994215088219967385)
              ·
                refine ⟨1196173495661316164975539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1594897994215088219967385 1196173495661316164975539)
                ·
                  refine ⟨1794260243491974247463309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196173495661316164975539 1794260243491974247463309)
                  ·
                    refine ⟨672847591309490342798741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1794260243491974247463309 672847591309490342798741)
                    ·
                      rfl

theorem cell22_1965549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_1965549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965549 prefixEnd_1965549 := by exact prefixLift 1965549
  have htrace : WordTrace (prefixWord ++ tailWord_1965549) baseStart_1965549 baseEnd_1965549 := by
    simpa [prefixWord, tailWord_1965549, baseEnd_1965549] using wordTrace_append hprefix tailTrace_1965549
  have hstable : (prefixWord ++ tailWord_1965549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965549).length < 2 ^ (prefixWord ++ tailWord_1965549).sum := by decide
  have hdescent : baseEnd_1965549 < baseStart_1965549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965567 : List Nat := [1, 1, 2, 2, 1, 2, 2, 11]
def baseStart_1965567 : Nat := 118140960795 + 1965567 * 2 ^ 59
def prefixEnd_1965567 : Nat := 4983230072969 + 3 ^ 40 * 1965567 * 2
def baseEnd_1965567 : Nat := 74761528119704921760965

theorem tailTrace_1965567 : CollatzResearch.WordTrace tailWord_1965567 prefixEnd_1965567 74761528119704921760965 := by
  unfold tailWord_1965567
  simp only [CollatzResearch.WordTrace]
  refine ⟨71690118070093925962894955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47793412046729283975263303 71690118070093925962894955)
  ·
    refine ⟨107535177105140888944342433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71690118070093925962894955 107535177105140888944342433)
    ·
      refine ⟨80651382828855666708256825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107535177105140888944342433 80651382828855666708256825)
      ·
        refine ⟨60488537121641750031192619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80651382828855666708256825 60488537121641750031192619)
        ·
          refine ⟨90732805682462625046788929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60488537121641750031192619 90732805682462625046788929)
          ·
            refine ⟨68049604261846968785091697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90732805682462625046788929 68049604261846968785091697)
            ·
              refine ⟨51037203196385226588818773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68049604261846968785091697 51037203196385226588818773)
              ·
                refine ⟨74761528119704921760965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 51037203196385226588818773 74761528119704921760965)
                ·
                  rfl

theorem cell22_1965567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 11].length) (baseStart_1965567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965567 prefixEnd_1965567 := by exact prefixLift 1965567
  have htrace : WordTrace (prefixWord ++ tailWord_1965567) baseStart_1965567 baseEnd_1965567 := by
    simpa [prefixWord, tailWord_1965567, baseEnd_1965567] using wordTrace_append hprefix tailTrace_1965567
  have hstable : (prefixWord ++ tailWord_1965567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965567).length < 2 ^ (prefixWord ++ tailWord_1965567).sum := by decide
  have hdescent : baseEnd_1965567 < baseStart_1965567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965622 : List Nat := [5, 1, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_1965622 : Nat := 118140960795 + 1965622 * 2 ^ 59
def prefixEnd_1965622 : Nat := 4983230072969 + 3 ^ 40 * 1965622 * 2
def baseEnd_1965622 : Nat := 672872580701342485723517

theorem tailTrace_1965622 : CollatzResearch.WordTrace tailWord_1965622 prefixEnd_1965622 672872580701342485723517 := by
  unfold tailWord_1965622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4480757755305916897259195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47794749389929780237431413 4480757755305916897259195)
  ·
    refine ⟨6721136632958875345888793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4480757755305916897259195 6721136632958875345888793)
    ·
      refine ⟨5040852474719156509416595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6721136632958875345888793 5040852474719156509416595)
      ·
        refine ⟨7561278712078734764124893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5040852474719156509416595 7561278712078734764124893)
        ·
          refine ⟨2835479517029525536546835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7561278712078734764124893 2835479517029525536546835)
          ·
            refine ⟨4253219275544288304820253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2835479517029525536546835 4253219275544288304820253)
            ·
              refine ⟨1594957228329108114307595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4253219275544288304820253 1594957228329108114307595)
              ·
                refine ⟨2392435842493662171461393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1594957228329108114307595 2392435842493662171461393)
                ·
                  refine ⟨1794326881870246628596045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2392435842493662171461393 1794326881870246628596045)
                  ·
                    refine ⟨672872580701342485723517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1794326881870246628596045 672872580701342485723517)
                    ·
                      rfl

theorem cell22_1965622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_1965622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965622 prefixEnd_1965622 := by exact prefixLift 1965622
  have htrace : WordTrace (prefixWord ++ tailWord_1965622) baseStart_1965622 baseEnd_1965622 := by
    simpa [prefixWord, tailWord_1965622, baseEnd_1965622] using wordTrace_append hprefix tailTrace_1965622
  have hstable : (prefixWord ++ tailWord_1965622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965622).length < 2 ^ (prefixWord ++ tailWord_1965622).sum := by decide
  have hdescent : baseEnd_1965622 < baseStart_1965622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965650 : List Nat := [3, 2, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_1965650 : Nat := 118140960795 + 1965650 * 2 ^ 59
def prefixEnd_1965650 : Nat := 4983230072969 + 3 ^ 40 * 1965650 * 2
def baseEnd_1965650 : Nat := 672882165673559746023431

theorem tailTrace_1965650 : CollatzResearch.WordTrace tailWord_1965650 prefixEnd_1965650 672882165673559746023431 := by
  unfold tailWord_1965650
  simp only [CollatzResearch.WordTrace]
  refine ⟨17923286332198307784541601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47795430219195487425444269 17923286332198307784541601)
  ·
    refine ⟨13442464749148730838406201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17923286332198307784541601 13442464749148730838406201)
    ·
      refine ⟨10081848561861548128804651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13442464749148730838406201 10081848561861548128804651)
      ·
        refine ⟨15122772842792322193206977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10081848561861548128804651 15122772842792322193206977)
        ·
          refine ⟨11342079632094241644905233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15122772842792322193206977 11342079632094241644905233)
          ·
            refine ⟨8506559724070681233678925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11342079632094241644905233 8506559724070681233678925)
            ·
              refine ⟨3189959896526505462629597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8506559724070681233678925 3189959896526505462629597)
              ·
                refine ⟨1196234961197439548486099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3189959896526505462629597 1196234961197439548486099)
                ·
                  refine ⟨1794352441796159322729149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196234961197439548486099 1794352441796159322729149)
                  ·
                    refine ⟨672882165673559746023431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1794352441796159322729149 672882165673559746023431)
                    ·
                      rfl

theorem cell22_1965650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_1965650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965650 prefixEnd_1965650 := by exact prefixLift 1965650
  have htrace : WordTrace (prefixWord ++ tailWord_1965650) baseStart_1965650 baseEnd_1965650 := by
    simpa [prefixWord, tailWord_1965650, baseEnd_1965650] using wordTrace_append hprefix tailTrace_1965650
  have hstable : (prefixWord ++ tailWord_1965650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965650).length < 2 ^ (prefixWord ++ tailWord_1965650).sum := by decide
  have hdescent : baseEnd_1965650 < baseStart_1965650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965693 : List Nat := [1, 4, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_1965693 : Nat := 118140960795 + 1965693 * 2 ^ 59
def prefixEnd_1965693 : Nat := 4983230072969 + 3 ^ 40 * 1965693 * 2
def baseEnd_1965693 : Nat := 672896885452321967198299

theorem tailTrace_1965693 : CollatzResearch.WordTrace tailWord_1965693 prefixEnd_1965693 672896885452321967198299 := by
  unfold tailWord_1965693
  simp only [CollatzResearch.WordTrace]
  refine ⟨71694713667637449481981733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47796475778424966321321155 71694713667637449481981733)
  ·
    refine ⟨13442758812682021777871575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71694713667637449481981733 13442758812682021777871575)
    ·
      refine ⟨20164138219023032666807363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13442758812682021777871575 20164138219023032666807363)
      ·
        refine ⟨30246207328534549000211045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20164138219023032666807363 30246207328534549000211045)
        ·
          refine ⟨5671163874100227937539571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30246207328534549000211045 5671163874100227937539571)
          ·
            refine ⟨8506745811150341906309357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5671163874100227937539571 8506745811150341906309357)
            ·
              refine ⟨3190029679181378214866009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8506745811150341906309357 3190029679181378214866009)
              ·
                refine ⟨2392522259386033661149507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3190029679181378214866009 2392522259386033661149507)
                ·
                  refine ⟨3588783389079050491724261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2392522259386033661149507 3588783389079050491724261)
                  ·
                    refine ⟨672896885452321967198299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3588783389079050491724261 672896885452321967198299)
                    ·
                      rfl

theorem cell22_1965693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_1965693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965693 prefixEnd_1965693 := by exact prefixLift 1965693
  have htrace : WordTrace (prefixWord ++ tailWord_1965693) baseStart_1965693 baseEnd_1965693 := by
    simpa [prefixWord, tailWord_1965693, baseEnd_1965693] using wordTrace_append hprefix tailTrace_1965693
  have hstable : (prefixWord ++ tailWord_1965693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965693).length < 2 ^ (prefixWord ++ tailWord_1965693).sum := by decide
  have hdescent : baseEnd_1965693 < baseStart_1965693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965706 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 3, 5]
def baseStart_1965706 : Nat := 118140960795 + 1965706 * 2 ^ 59
def prefixEnd_1965706 : Nat := 4983230072969 + 3 ^ 40 * 1965706 * 2
def baseEnd_1965706 : Nat := 672901335617994266623259

theorem tailTrace_1965706 : CollatzResearch.WordTrace tailWord_1965706 prefixEnd_1965706 672901335617994266623259 := by
  unfold tailWord_1965706
  simp only [CollatzResearch.WordTrace]
  refine ⟨17923796954147588175551243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47796791877726901801469981 17923796954147588175551243)
  ·
    refine ⟨26885695431221382263326865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17923796954147588175551243 26885695431221382263326865)
    ·
      refine ⟨20164271573416036697495149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26885695431221382263326865 20164271573416036697495149)
      ·
        refine ⟨7561601840031013761560681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20164271573416036697495149 7561601840031013761560681)
        ·
          refine ⟨5671201380023260321170511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7561601840031013761560681 5671201380023260321170511)
          ·
            refine ⟨8506802070034890481755767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5671201380023260321170511 8506802070034890481755767)
            ·
              refine ⟨12760203105052335722633651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8506802070034890481755767 12760203105052335722633651)
              ·
                refine ⟨19140304657578503583950477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12760203105052335722633651 19140304657578503583950477)
                ·
                  refine ⟨7177614246591938843981429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19140304657578503583950477 7177614246591938843981429)
                  ·
                    refine ⟨672901335617994266623259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7177614246591938843981429 672901335617994266623259)
                    ·
                      rfl

theorem cell22_1965706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_1965706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965706 prefixEnd_1965706 := by exact prefixLift 1965706
  have htrace : WordTrace (prefixWord ++ tailWord_1965706) baseStart_1965706 baseEnd_1965706 := by
    simpa [prefixWord, tailWord_1965706, baseEnd_1965706] using wordTrace_append hprefix tailTrace_1965706
  have hstable : (prefixWord ++ tailWord_1965706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965706).length < 2 ^ (prefixWord ++ tailWord_1965706).sum := by decide
  have hdescent : baseEnd_1965706 < baseStart_1965706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965710 : List Nat := [4, 1, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_1965710 : Nat := 118140960795 + 1965710 * 2 ^ 59
def prefixEnd_1965710 : Nat := 4983230072969 + 3 ^ 40 * 1965710 * 2
def baseEnd_1965710 : Nat := 672902704899739589523247

theorem tailTrace_1965710 : CollatzResearch.WordTrace tailWord_1965710 prefixEnd_1965710 672902704899739589523247 := by
  unfold tailWord_1965710
  simp only [CollatzResearch.WordTrace]
  refine ⟨8961916713571982673168823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47796889139050574256900389 8961916713571982673168823)
  ·
    refine ⟨13442875070357974009753235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8961916713571982673168823 13442875070357974009753235)
    ·
      refine ⟨20164312605536961014629853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13442875070357974009753235 20164312605536961014629853)
      ·
        refine ⟨7561617227076360380486195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20164312605536961014629853 7561617227076360380486195)
        ·
          refine ⟨11342425840614540570729293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7561617227076360380486195 11342425840614540570729293)
          ·
            refine ⟨4253409690230452714023485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11342425840614540570729293 4253409690230452714023485)
            ·
              refine ⟨1595028633836419767758807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4253409690230452714023485 1595028633836419767758807)
              ·
                refine ⟨2392542950754629651638211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595028633836419767758807 2392542950754629651638211)
                ·
                  refine ⟨3588814426131944477457317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2392542950754629651638211 3588814426131944477457317)
                  ·
                    refine ⟨672902704899739589523247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3588814426131944477457317 672902704899739589523247)
                    ·
                      rfl

theorem cell22_1965710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_1965710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965710 prefixEnd_1965710 := by exact prefixLift 1965710
  have htrace : WordTrace (prefixWord ++ tailWord_1965710) baseStart_1965710 baseEnd_1965710 := by
    simpa [prefixWord, tailWord_1965710, baseEnd_1965710] using wordTrace_append hprefix tailTrace_1965710
  have hstable : (prefixWord ++ tailWord_1965710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965710).length < 2 ^ (prefixWord ++ tailWord_1965710).sum := by decide
  have hdescent : baseEnd_1965710 < baseStart_1965710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965719 : List Nat := [1, 1, 3, 3, 2, 12]
def baseStart_1965719 : Nat := 118140960795 + 1965719 * 2 ^ 59
def prefixEnd_1965719 : Nat := 4983230072969 + 3 ^ 40 * 1965719 * 2
def baseEnd_1965719 : Nat := 8307478836835389704299

theorem tailTrace_1965719 : CollatzResearch.WordTrace tailWord_1965719 prefixEnd_1965719 8307478836835389704299 := by
  unfold tailWord_1965719
  simp only [CollatzResearch.WordTrace]
  refine ⟨71695661965543255922428211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47797107977028837281618807 71695661965543255922428211)
  ·
    refine ⟨107543492948314883883642317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71695661965543255922428211 107543492948314883883642317)
    ·
      refine ⟨40328809855618081456365869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107543492948314883883642317 40328809855618081456365869)
      ·
        refine ⟨15123303695856780546137201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40328809855618081456365869 15123303695856780546137201)
        ·
          refine ⟨11342477771892585409602901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15123303695856780546137201 11342477771892585409602901)
          ·
            refine ⟨8307478836835389704299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 11342477771892585409602901 8307478836835389704299)
            ·
              rfl

theorem cell22_1965719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 12].length) (baseStart_1965719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965719 prefixEnd_1965719 := by exact prefixLift 1965719
  have htrace : WordTrace (prefixWord ++ tailWord_1965719) baseStart_1965719 baseEnd_1965719 := by
    simpa [prefixWord, tailWord_1965719, baseEnd_1965719] using wordTrace_append hprefix tailTrace_1965719
  have hstable : (prefixWord ++ tailWord_1965719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965719).length < 2 ^ (prefixWord ++ tailWord_1965719).sum := by decide
  have hdescent : baseEnd_1965719 < baseStart_1965719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965785 : List Nat := [1, 2, 1, 2, 3, 3, 2, 4, 1, 3]
def baseStart_1965785 : Nat := 118140960795 + 1965785 * 2 ^ 59
def prefixEnd_1965785 : Nat := 4983230072969 + 3 ^ 40 * 1965785 * 2
def baseEnd_1965785 : Nat := 672928378932464393898017

theorem tailTrace_1965785 : CollatzResearch.WordTrace tailWord_1965785 prefixEnd_1965785 672928378932464393898017 := by
  unfold tailWord_1965785
  simp only [CollatzResearch.WordTrace]
  refine ⟨71698069183304149194330809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47798712788869432796220539 71698069183304149194330809)
  ·
    refine ⟨53773551887478111895748107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71698069183304149194330809 53773551887478111895748107)
    ·
      refine ⟨80660327831217167843622161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53773551887478111895748107 80660327831217167843622161)
      ·
        refine ⟨60495245873412875882716621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80660327831217167843622161 60495245873412875882716621)
        ·
          refine ⟨22685717202529828456018733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60495245873412875882716621 22685717202529828456018733)
          ·
            refine ⟨8507143950948685671007025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22685717202529828456018733 8507143950948685671007025)
            ·
              refine ⟨6380357963211514253255269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8507143950948685671007025 6380357963211514253255269)
              ·
                refine ⟨1196317118102158922485363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6380357963211514253255269 1196317118102158922485363)
                ·
                  refine ⟨1794475677153238383728045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196317118102158922485363 1794475677153238383728045)
                  ·
                    refine ⟨672928378932464393898017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1794475677153238383728045 672928378932464393898017)
                    ·
                      rfl

theorem cell22_1965785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 1, 3].length) (baseStart_1965785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965785 prefixEnd_1965785 := by exact prefixLift 1965785
  have htrace : WordTrace (prefixWord ++ tailWord_1965785) baseStart_1965785 baseEnd_1965785 := by
    simpa [prefixWord, tailWord_1965785, baseEnd_1965785] using wordTrace_append hprefix tailTrace_1965785
  have hstable : (prefixWord ++ tailWord_1965785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965785).length < 2 ^ (prefixWord ++ tailWord_1965785).sum := by decide
  have hdescent : baseEnd_1965785 < baseStart_1965785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965796 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_1965796 : Nat := 118140960795 + 1965796 * 2 ^ 59
def prefixEnd_1965796 : Nat := 4983230072969 + 3 ^ 40 * 1965796 * 2
def baseEnd_1965796 : Nat := 672932144457264031872983

theorem tailTrace_1965796 : CollatzResearch.WordTrace tailWord_1965796 prefixEnd_1965796 672932144457264031872983 := by
  unfold tailWord_1965796
  simp only [CollatzResearch.WordTrace]
  refine ⟨35849235193132149036490621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47798980257509532048654161 35849235193132149036490621)
  ·
    refine ⟨13443463197424555888683983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35849235193132149036490621 13443463197424555888683983)
    ·
      refine ⟨20165194796136833833025975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13443463197424555888683983 20165194796136833833025975)
      ·
        refine ⟨30247792194205250749538963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20165194796136833833025975 30247792194205250749538963)
        ·
          refine ⟨45371688291307876124308445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30247792194205250749538963 45371688291307876124308445)
          ·
            refine ⟨17014383109240453546615667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45371688291307876124308445 17014383109240453546615667)
            ·
              refine ⟨25521574663860680319923501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17014383109240453546615667 25521574663860680319923501)
              ·
                refine ⟨9570590498947755119971313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25521574663860680319923501 9570590498947755119971313)
                ·
                  refine ⟨7177942874210816339978485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9570590498947755119971313 7177942874210816339978485)
                  ·
                    refine ⟨672932144457264031872983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7177942874210816339978485 672932144457264031872983)
                    ·
                      rfl

theorem cell22_1965796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_1965796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965796 prefixEnd_1965796 := by exact prefixLift 1965796
  have htrace : WordTrace (prefixWord ++ tailWord_1965796) baseStart_1965796 baseEnd_1965796 := by
    simpa [prefixWord, tailWord_1965796, baseEnd_1965796] using wordTrace_append hprefix tailTrace_1965796
  have hstable : (prefixWord ++ tailWord_1965796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965796).length < 2 ^ (prefixWord ++ tailWord_1965796).sum := by decide
  have hdescent : baseEnd_1965796 < baseStart_1965796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965811 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 3, 4]
def baseStart_1965811 : Nat := 118140960795 + 1965811 * 2 ^ 59
def prefixEnd_1965811 : Nat := 4983230072969 + 3 ^ 40 * 1965811 * 2
def baseEnd_1965811 : Nat := 672937279263808992747937

theorem tailTrace_1965811 : CollatzResearch.WordTrace tailWord_1965811 prefixEnd_1965811 672937279263808992747937 := by
  unfold tailWord_1965811
  simp only [CollatzResearch.WordTrace]
  refine ⟨71699017481209955634777287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47799344987473303756518191 71699017481209955634777287)
  ·
    refine ⟨107548526221814933452165931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71699017481209955634777287 107548526221814933452165931)
    ·
      refine ⟨161322789332722400178248897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107548526221814933452165931 161322789332722400178248897)
      ·
        refine ⟨120992091999541800133686673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161322789332722400178248897 120992091999541800133686673)
        ·
          refine ⟨90744068999656350100265005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120992091999541800133686673 90744068999656350100265005)
          ·
            refine ⟨34029025874871131287599377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90744068999656350100265005 34029025874871131287599377)
            ·
              refine ⟨25521769406153348465699533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34029025874871131287599377 25521769406153348465699533)
              ·
                refine ⟨9570663527307505674637325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25521769406153348465699533 9570663527307505674637325)
                ·
                  refine ⟨3588998822740314627988997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9570663527307505674637325 3588998822740314627988997)
                  ·
                    refine ⟨672937279263808992747937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3588998822740314627988997 672937279263808992747937)
                    ·
                      rfl

theorem cell22_1965811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 4].length) (baseStart_1965811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965811 prefixEnd_1965811 := by exact prefixLift 1965811
  have htrace : WordTrace (prefixWord ++ tailWord_1965811) baseStart_1965811 baseEnd_1965811 := by
    simpa [prefixWord, tailWord_1965811, baseEnd_1965811] using wordTrace_append hprefix tailTrace_1965811
  have hstable : (prefixWord ++ tailWord_1965811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965811).length < 2 ^ (prefixWord ++ tailWord_1965811).sum := by decide
  have hdescent : baseEnd_1965811 < baseStart_1965811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965858 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1965858 : Nat := 118140960795 + 1965858 * 2 ^ 59
def prefixEnd_1965858 : Nat := 4983230072969 + 3 ^ 40 * 1965858 * 2
def baseEnd_1965858 : Nat := 672953368324316536822793

theorem tailTrace_1965858 : CollatzResearch.WordTrace tailWord_1965858 prefixEnd_1965858 672953368324316536822793 := by
  unfold tailWord_1965858
  simp only [CollatzResearch.WordTrace]
  refine ⟨17925182928009920665434557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47800487808026455107825485 17925182928009920665434557)
  ·
    refine ⟨6721943598003720249537959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17925182928009920665434557 6721943598003720249537959)
    ·
      refine ⟨10082915397005580374306939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6721943598003720249537959 10082915397005580374306939)
      ·
        refine ⟨15124373095508370561460409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10082915397005580374306939 15124373095508370561460409)
        ·
          refine ⟨11343279821631277921095307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15124373095508370561460409 11343279821631277921095307)
          ·
            refine ⟨17014919732446916881642961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11343279821631277921095307 17014919732446916881642961)
            ·
              refine ⟨12761189799335187661232221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17014919732446916881642961 12761189799335187661232221)
              ·
                refine ⟨4785446174750695372962083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12761189799335187661232221 4785446174750695372962083)
                ·
                  refine ⟨7178169262126043059443125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4785446174750695372962083 7178169262126043059443125)
                  ·
                    refine ⟨672953368324316536822793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7178169262126043059443125 672953368324316536822793)
                    ·
                      rfl

theorem cell22_1965858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1965858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965858 prefixEnd_1965858 := by exact prefixLift 1965858
  have htrace : WordTrace (prefixWord ++ tailWord_1965858) baseStart_1965858 baseEnd_1965858 := by
    simpa [prefixWord, tailWord_1965858, baseEnd_1965858] using wordTrace_append hprefix tailTrace_1965858
  have hstable : (prefixWord ++ tailWord_1965858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965858).length < 2 ^ (prefixWord ++ tailWord_1965858).sum := by decide
  have hdescent : baseEnd_1965858 < baseStart_1965858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965873 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 2, 4]
def baseStart_1965873 : Nat := 118140960795 + 1965873 * 2 ^ 59
def prefixEnd_1965873 : Nat := 4983230072969 + 3 ^ 40 * 1965873 * 2
def baseEnd_1965873 : Nat := 672958503130861497697747

theorem tailTrace_1965873 : CollatzResearch.WordTrace tailWord_1965873 prefixEnd_1965873 672958503130861497697747 := by
  unfold tailWord_1965873
  simp only [CollatzResearch.WordTrace]
  refine ⟨71701278806985340223534273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47800852537990226815689515 71701278806985340223534273)
  ·
    refine ⟨53775959105239005167650705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71701278806985340223534273 53775959105239005167650705)
    ·
      refine ⟨40331969328929253875738029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53775959105239005167650705 40331969328929253875738029)
      ·
        refine ⟨15124488498348470203401761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40331969328929253875738029 15124488498348470203401761)
        ·
          refine ⟨11343366373761352652551321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15124488498348470203401761 11343366373761352652551321)
          ·
            refine ⟨8507524780321014489413491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11343366373761352652551321 8507524780321014489413491)
            ·
              refine ⟨12761287170481521734120237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8507524780321014489413491 12761287170481521734120237)
              ·
                refine ⟨4785482688930570650295089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12761287170481521734120237 4785482688930570650295089)
                ·
                  refine ⟨3589112016697927987721317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4785482688930570650295089 3589112016697927987721317)
                  ·
                    refine ⟨672958503130861497697747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3589112016697927987721317 672958503130861497697747)
                    ·
                      rfl

theorem cell22_1965873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_1965873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965873 prefixEnd_1965873 := by exact prefixLift 1965873
  have htrace : WordTrace (prefixWord ++ tailWord_1965873) baseStart_1965873 baseEnd_1965873 := by
    simpa [prefixWord, tailWord_1965873, baseEnd_1965873] using wordTrace_append hprefix tailTrace_1965873
  have hstable : (prefixWord ++ tailWord_1965873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965873).length < 2 ^ (prefixWord ++ tailWord_1965873).sum := by decide
  have hdescent : baseEnd_1965873 < baseStart_1965873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965894 : List Nat := [6, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_1965894 : Nat := 118140960795 + 1965894 * 2 ^ 59
def prefixEnd_1965894 : Nat := 4983230072969 + 3 ^ 40 * 1965894 * 2
def baseEnd_1965894 : Nat := 224321897286674814307561

theorem tailTrace_1965894 : CollatzResearch.WordTrace tailWord_1965894 prefixEnd_1965894 224321897286674814307561 := by
  unfold tailWord_1965894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2240688898122164400314023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47801363159939507206699157 2240688898122164400314023)
  ·
    refine ⟨3361033347183246600471035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2240688898122164400314023 3361033347183246600471035)
    ·
      refine ⟨5041550020774869900706553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3361033347183246600471035 5041550020774869900706553)
      ·
        refine ⟨3781162515581152425529915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5041550020774869900706553 3781162515581152425529915)
        ·
          refine ⟨5671743773371728638294873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3781162515581152425529915 5671743773371728638294873)
          ·
            refine ⟨4253807830028796478721155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5671743773371728638294873 4253807830028796478721155)
            ·
              refine ⟨6380711745043194718081733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4253807830028796478721155 6380711745043194718081733)
              ·
                refine ⟨1196383452195599009640325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6380711745043194718081733 1196383452195599009640325)
                ·
                  refine ⟨224321897286674814307561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1196383452195599009640325 224321897286674814307561)
                  ·
                    rfl

theorem cell22_1965894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_1965894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965894 prefixEnd_1965894 := by exact prefixLift 1965894
  have htrace : WordTrace (prefixWord ++ tailWord_1965894) baseStart_1965894 baseEnd_1965894 := by
    simpa [prefixWord, tailWord_1965894, baseEnd_1965894] using wordTrace_append hprefix tailTrace_1965894
  have hstable : (prefixWord ++ tailWord_1965894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965894).length < 2 ^ (prefixWord ++ tailWord_1965894).sum := by decide
  have hdescent : baseEnd_1965894 < baseStart_1965894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965920 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 3, 3]
def baseStart_1965920 : Nat := 118140960795 + 1965920 * 2 ^ 59
def prefixEnd_1965920 : Nat := 4983230072969 + 3 ^ 40 * 1965920 * 2
def baseEnd_1965920 : Nat := 672974592191369041772603

theorem tailTrace_1965920 : CollatzResearch.WordTrace tailWord_1965920 prefixEnd_1965920 672974592191369041772603 := by
  unfold tailWord_1965920
  simp only [CollatzResearch.WordTrace]
  refine ⟨35851496518907533625247607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47801995358543378166996809 35851496518907533625247607)
  ·
    refine ⟨53777244778361300437871411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35851496518907533625247607 53777244778361300437871411)
    ·
      refine ⟨80665867167541950656807117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53777244778361300437871411 80665867167541950656807117)
      ·
        refine ⟨30249700187828231496302669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80665867167541950656807117 30249700187828231496302669)
        ·
          refine ⟨11343637570435586811113501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30249700187828231496302669 11343637570435586811113501)
          ·
            refine ⟨4253864088913345054167563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11343637570435586811113501 4253864088913345054167563)
            ·
              refine ⟨6380796133370017581251345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4253864088913345054167563 6380796133370017581251345)
              ·
                refine ⟨4785597100027513185938509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6380796133370017581251345 4785597100027513185938509)
                ·
                  refine ⟨1794598912510317444726941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4785597100027513185938509 1794598912510317444726941)
                  ·
                    refine ⟨672974592191369041772603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1794598912510317444726941 672974592191369041772603)
                    ·
                      rfl

theorem cell22_1965920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 3, 3].length) (baseStart_1965920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965920 prefixEnd_1965920 := by exact prefixLift 1965920
  have htrace : WordTrace (prefixWord ++ tailWord_1965920) baseStart_1965920 baseEnd_1965920 := by
    simpa [prefixWord, tailWord_1965920, baseEnd_1965920] using wordTrace_append hprefix tailTrace_1965920
  have hstable : (prefixWord ++ tailWord_1965920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965920).length < 2 ^ (prefixWord ++ tailWord_1965920).sum := by decide
  have hdescent : baseEnd_1965920 < baseStart_1965920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965931 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 3, 7]
def baseStart_1965931 : Nat := 118140960795 + 1965931 * 2 ^ 59
def prefixEnd_1965931 : Nat := 4983230072969 + 3 ^ 40 * 1965931 * 2
def baseEnd_1965931 : Nat := 672978357716168679747569

theorem tailTrace_1965931 : CollatzResearch.WordTrace tailWord_1965931 prefixEnd_1965931 672978357716168679747569 := by
  unfold tailWord_1965931
  simp only [CollatzResearch.WordTrace]
  refine ⟨71703394240775216129145647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47802262827183477419430431 71703394240775216129145647)
  ·
    refine ⟨107555091361162824193718471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71703394240775216129145647 107555091361162824193718471)
    ·
      refine ⟨161332637041744236290577707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107555091361162824193718471 161332637041744236290577707)
      ·
        refine ⟨241998955562616354435866561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161332637041744236290577707 241998955562616354435866561)
        ·
          refine ⟨181499216671962265826899921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241998955562616354435866561 181499216671962265826899921)
          ·
            refine ⟨136124412503971699370174941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181499216671962265826899921 136124412503971699370174941)
            ·
              refine ⟨51046654688989387263815603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136124412503971699370174941 51046654688989387263815603)
              ·
                refine ⟨76569982033484080895723405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51046654688989387263815603 76569982033484080895723405)
                ·
                  refine ⟨28713743262556530335896277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76569982033484080895723405 28713743262556530335896277)
                  ·
                    refine ⟨672978357716168679747569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28713743262556530335896277 672978357716168679747569)
                    ·
                      rfl

theorem cell22_1965931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_1965931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965931 prefixEnd_1965931 := by exact prefixLift 1965931
  have htrace : WordTrace (prefixWord ++ tailWord_1965931) baseStart_1965931 baseEnd_1965931 := by
    simpa [prefixWord, tailWord_1965931, baseEnd_1965931] using wordTrace_append hprefix tailTrace_1965931
  have hstable : (prefixWord ++ tailWord_1965931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965931).length < 2 ^ (prefixWord ++ tailWord_1965931).sum := by decide
  have hdescent : baseEnd_1965931 < baseStart_1965931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1965937 : List Nat := [1, 2, 2, 2, 1, 3, 4, 3, 1, 3]
def baseStart_1965937 : Nat := 118140960795 + 1965937 * 2 ^ 59
def prefixEnd_1965937 : Nat := 4983230072969 + 3 ^ 40 * 1965937 * 2
def baseEnd_1965937 : Nat := 672980411638786664097551

theorem tailTrace_1965937 : CollatzResearch.WordTrace tailWord_1965937 prefixEnd_1965937 672980411638786664097551 := by
  unfold tailWord_1965937
  simp only [CollatzResearch.WordTrace]
  refine ⟨71703613078753479153864065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47802408719168986102576043 71703613078753479153864065)
  ·
    refine ⟨53777709809065109365398049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71703613078753479153864065 53777709809065109365398049)
    ·
      refine ⟨40333282356798832024048537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53777709809065109365398049 40333282356798832024048537)
      ·
        refine ⟨30249961767599124018036403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40333282356798832024048537 30249961767599124018036403)
        ·
          refine ⟨45374942651398686027054605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30249961767599124018036403 45374942651398686027054605)
          ·
            refine ⟨17015603494274507260145477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45374942651398686027054605 17015603494274507260145477)
            ·
              refine ⟨3190425655176470111277277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17015603494274507260145477 3190425655176470111277277)
              ·
                refine ⟨1196409620691176291728979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3190425655176470111277277 1196409620691176291728979)
                ·
                  refine ⟨1794614431036764437593469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196409620691176291728979 1794614431036764437593469)
                  ·
                    refine ⟨672980411638786664097551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1794614431036764437593469 672980411638786664097551)
                    ·
                      rfl

theorem cell22_1965937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_1965937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1965937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1965937 prefixEnd_1965937 := by exact prefixLift 1965937
  have htrace : WordTrace (prefixWord ++ tailWord_1965937) baseStart_1965937 baseEnd_1965937 := by
    simpa [prefixWord, tailWord_1965937, baseEnd_1965937] using wordTrace_append hprefix tailTrace_1965937
  have hstable : (prefixWord ++ tailWord_1965937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1965937).length < 2 ^ (prefixWord ++ tailWord_1965937).sum := by decide
  have hdescent : baseEnd_1965937 < baseStart_1965937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1965937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966042 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 2, 4]
def baseStart_1966042 : Nat := 118140960795 + 1966042 * 2 ^ 59
def prefixEnd_1966042 : Nat := 4983230072969 + 3 ^ 40 * 1966042 * 2
def baseEnd_1966042 : Nat := 673016355284601390222229

theorem tailTrace_1966042 : CollatzResearch.WordTrace tailWord_1966042 prefixEnd_1966042 673016355284601390222229 := by
  unfold tailWord_1966042
  simp only [CollatzResearch.WordTrace]
  refine ⟨17926860685843270521609095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47804961828915388057624253 17926860685843270521609095)
  ·
    refine ⟨26890291028764905782413643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17926860685843270521609095 26890291028764905782413643)
    ·
      refine ⟨40335436543147358673620465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26890291028764905782413643 40335436543147358673620465)
      ·
        refine ⟨30251577407360519005215349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40335436543147358673620465 30251577407360519005215349)
        ·
          refine ⟨2836085381940048656738939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30251577407360519005215349 2836085381940048656738939)
          ·
            refine ⟨4254128072910072985108409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836085381940048656738939 4254128072910072985108409)
            ·
              refine ⟨3190596054682554738831307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4254128072910072985108409 3190596054682554738831307)
              ·
                refine ⟨4785894082023832108246961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3190596054682554738831307 4785894082023832108246961)
                ·
                  refine ⟨3589420561517874081185221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4785894082023832108246961 3589420561517874081185221)
                  ·
                    refine ⟨673016355284601390222229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3589420561517874081185221 673016355284601390222229)
                    ·
                      rfl

theorem cell22_1966042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_1966042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966042 prefixEnd_1966042 := by exact prefixLift 1966042
  have htrace : WordTrace (prefixWord ++ tailWord_1966042) baseStart_1966042 baseEnd_1966042 := by
    simpa [prefixWord, tailWord_1966042, baseEnd_1966042] using wordTrace_append hprefix tailTrace_1966042
  have hstable : (prefixWord ++ tailWord_1966042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966042).length < 2 ^ (prefixWord ++ tailWord_1966042).sum := by decide
  have hdescent : baseEnd_1966042 < baseStart_1966042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966061 : List Nat := [1, 5, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_1966061 : Nat := 118140960795 + 1966061 * 2 ^ 59
def prefixEnd_1966061 : Nat := 4983230072969 + 3 ^ 40 * 1966061 * 2
def baseEnd_1966061 : Nat := 673022859372891673997171

theorem tailTrace_1966061 : CollatzResearch.WordTrace tailWord_1966061 prefixEnd_1966061 673022859372891673997171 := by
  unfold tailWord_1966061
  simp only [CollatzResearch.WordTrace]
  refine ⟨71708135730304248331378037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47805423820202832220918691 71708135730304248331378037)
  ·
    refine ⟨6722637724716023281066691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71708135730304248331378037 6722637724716023281066691)
    ·
      refine ⟨10083956587074034921600037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6722637724716023281066691 10083956587074034921600037)
      ·
        refine ⟨1890741860076381547800007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10083956587074034921600037 1890741860076381547800007)
        ·
          refine ⟨2836112790114572321700011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890741860076381547800007 2836112790114572321700011)
          ·
            refine ⟨4254169185171858482550017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836112790114572321700011 4254169185171858482550017)
            ·
              refine ⟨3190626888878893861912513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4254169185171858482550017 3190626888878893861912513)
              ·
                refine ⟨2392970166659170396434385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3190626888878893861912513 2392970166659170396434385)
                ·
                  refine ⟨1794727624994377797325789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2392970166659170396434385 1794727624994377797325789)
                  ·
                    refine ⟨673022859372891673997171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1794727624994377797325789 673022859372891673997171)
                    ·
                      rfl

theorem cell22_1966061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_1966061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966061 prefixEnd_1966061 := by exact prefixLift 1966061
  have htrace : WordTrace (prefixWord ++ tailWord_1966061) baseStart_1966061 baseEnd_1966061 := by
    simpa [prefixWord, tailWord_1966061, baseEnd_1966061] using wordTrace_append hprefix tailTrace_1966061
  have hstable : (prefixWord ++ tailWord_1966061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966061).length < 2 ^ (prefixWord ++ tailWord_1966061).sum := by decide
  have hdescent : baseEnd_1966061 < baseStart_1966061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966085 : List Nat := [1, 3, 1, 1, 2, 4, 2, 3, 5]
def baseStart_1966085 : Nat := 118140960795 + 1966085 * 2 ^ 59
def prefixEnd_1966085 : Nat := 4983230072969 + 3 ^ 40 * 1966085 * 2
def baseEnd_1966085 : Nat := 224343691687787870465699

theorem tailTrace_1966085 : CollatzResearch.WordTrace tailWord_1966085 prefixEnd_1966085 224343691687787870465699 := by
  unfold tailWord_1966085
  simp only [CollatzResearch.WordTrace]
  refine ⟨71709011082217300430251709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47806007388144866953501139 71709011082217300430251709)
  ·
    refine ⟨26890879155831487661344391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71709011082217300430251709 26890879155831487661344391)
    ·
      refine ⟨40336318733747231492016587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26890879155831487661344391 40336318733747231492016587)
      ·
        refine ⟨60504478100620847238024881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40336318733747231492016587 60504478100620847238024881)
        ·
          refine ⟨45378358575465635428518661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60504478100620847238024881 45378358575465635428518661)
          ·
            refine ⟨8508442232899806642847249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45378358575465635428518661 8508442232899806642847249)
            ·
              refine ⟨6381331674674854982135437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8508442232899806642847249 6381331674674854982135437)
              ·
                refine ⟨2392999378003070618300789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6381331674674854982135437 2392999378003070618300789)
                ·
                  refine ⟨224343691687787870465699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2392999378003070618300789 224343691687787870465699)
                  ·
                    rfl

theorem cell22_1966085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_1966085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966085 prefixEnd_1966085 := by exact prefixLift 1966085
  have htrace : WordTrace (prefixWord ++ tailWord_1966085) baseStart_1966085 baseEnd_1966085 := by
    simpa [prefixWord, tailWord_1966085, baseEnd_1966085] using wordTrace_append hprefix tailTrace_1966085
  have hstable : (prefixWord ++ tailWord_1966085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966085).length < 2 ^ (prefixWord ++ tailWord_1966085).sum := by decide
  have hdescent : baseEnd_1966085 < baseStart_1966085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966093 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1966093 : Nat := 118140960795 + 1966093 * 2 ^ 59
def prefixEnd_1966093 : Nat := 4983230072969 + 3 ^ 40 * 1966093 * 2
def baseEnd_1966093 : Nat := 673033813626854257197073

theorem tailTrace_1966093 : CollatzResearch.WordTrace tailWord_1966093 prefixEnd_1966093 673033813626854257197073 := by
  unfold tailWord_1966093
  simp only [CollatzResearch.WordTrace]
  refine ⟨71709302866188317796542933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47806201910792211864361955 71709302866188317796542933)
  ·
    refine ⟨1680686785926288698356475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 71709302866188317796542933 1680686785926288698356475)
    ·
      refine ⟨2521030178889433047534713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1680686785926288698356475 2521030178889433047534713)
      ·
        refine ⟨1890772634167074785651035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2521030178889433047534713 1890772634167074785651035)
        ·
          refine ⟨2836158951250612178476553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1890772634167074785651035 2836158951250612178476553)
          ·
            refine ⟨2127119213437959133857415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2836158951250612178476553 2127119213437959133857415)
            ·
              refine ⟨3190678820156938700786123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127119213437959133857415 3190678820156938700786123)
              ·
                refine ⟨4786018230235408051179185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3190678820156938700786123 4786018230235408051179185)
                ·
                  refine ⟨3589513672676556038384389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4786018230235408051179185 3589513672676556038384389)
                  ·
                    refine ⟨673033813626854257197073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3589513672676556038384389 673033813626854257197073)
                    ·
                      rfl

theorem cell22_1966093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1966093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966093 prefixEnd_1966093 := by exact prefixLift 1966093
  have htrace : WordTrace (prefixWord ++ tailWord_1966093) baseStart_1966093 baseEnd_1966093 := by
    simpa [prefixWord, tailWord_1966093, baseEnd_1966093] using wordTrace_append hprefix tailTrace_1966093
  have hstable : (prefixWord ++ tailWord_1966093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966093).length < 2 ^ (prefixWord ++ tailWord_1966093).sum := by decide
  have hdescent : baseEnd_1966093 < baseStart_1966093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966130 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 6]
def baseStart_1966130 : Nat := 118140960795 + 1966130 * 2 ^ 59
def prefixEnd_1966130 : Nat := 4983230072969 + 3 ^ 40 * 1966130 * 2
def baseEnd_1966130 : Nat := 224348826494332831340653

theorem tailTrace_1966130 : CollatzResearch.WordTrace tailWord_1966130 prefixEnd_1966130 224348826494332831340653 := by
  unfold tailWord_1966130
  simp only [CollatzResearch.WordTrace]
  refine ⟨17927663091763568278909961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47807101578036182077093229 17927663091763568278909961)
  ·
    refine ⟨13445747318822676209182471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17927663091763568278909961 13445747318822676209182471)
    ·
      refine ⟨20168620978234014313773707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13445747318822676209182471 20168620978234014313773707)
      ·
        refine ⟨30252931467351021470660561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20168620978234014313773707 30252931467351021470660561)
        ·
          refine ⟨22689698600513266102995421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30252931467351021470660561 22689698600513266102995421)
          ·
            refine ⟨8508636975192474788623283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22689698600513266102995421 8508636975192474788623283)
            ·
              refine ⟨12762955462788712182934925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8508636975192474788623283 12762955462788712182934925)
              ·
                refine ⟨4786108298545767068600597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12762955462788712182934925 4786108298545767068600597)
                ·
                  refine ⟨224348826494332831340653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4786108298545767068600597 224348826494332831340653)
                  ·
                    rfl

theorem cell22_1966130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_1966130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966130 prefixEnd_1966130 := by exact prefixLift 1966130
  have htrace : WordTrace (prefixWord ++ tailWord_1966130) baseStart_1966130 baseEnd_1966130 := by
    simpa [prefixWord, tailWord_1966130, baseEnd_1966130] using wordTrace_append hprefix tailTrace_1966130
  have hstable : (prefixWord ++ tailWord_1966130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966130).length < 2 ^ (prefixWord ++ tailWord_1966130).sum := by decide
  have hdescent : baseEnd_1966130 < baseStart_1966130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966166 : List Nat := [5, 2, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1966166 : Nat := 118140960795 + 1966166 * 2 ^ 59
def prefixEnd_1966166 : Nat := 4983230072969 + 3 ^ 40 * 1966166 * 2
def baseEnd_1966166 : Nat := 673058803018706400121849

theorem tailTrace_1966166 : CollatzResearch.WordTrace tailWord_1966166 prefixEnd_1966166 673058803018706400121849 := by
  unfold tailWord_1966166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4481997837182740703996897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47807976929949234175966901 4481997837182740703996897)
  ·
    refine ⟨3361498377887055527997673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4481997837182740703996897 3361498377887055527997673)
    ·
      refine ⟨2521123783415291645998255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3361498377887055527997673 2521123783415291645998255)
      ·
        refine ⟨3781685675122937468997383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2521123783415291645998255 3781685675122937468997383)
        ·
          refine ⟨5672528512684406203496075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3781685675122937468997383 5672528512684406203496075)
          ·
            refine ⟨8508792769026609305244113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5672528512684406203496075 8508792769026609305244113)
            ·
              refine ⟨6381594576769956978933085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8508792769026609305244113 6381594576769956978933085)
              ·
                refine ⟨2393097966288733867099907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6381594576769956978933085 2393097966288733867099907)
                ·
                  refine ⟨3589646949433100800649861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393097966288733867099907 3589646949433100800649861)
                  ·
                    refine ⟨673058803018706400121849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3589646949433100800649861 673058803018706400121849)
                    ·
                      rfl

theorem cell22_1966166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1966166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966166 prefixEnd_1966166 := by exact prefixLift 1966166
  have htrace : WordTrace (prefixWord ++ tailWord_1966166) baseStart_1966166 baseEnd_1966166 := by
    simpa [prefixWord, tailWord_1966166, baseEnd_1966166] using wordTrace_append hprefix tailTrace_1966166
  have hstable : (prefixWord ++ tailWord_1966166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966166).length < 2 ^ (prefixWord ++ tailWord_1966166).sum := by decide
  have hdescent : baseEnd_1966166 < baseStart_1966166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966224 : List Nat := [2, 1, 1, 1, 1, 1, 6, 5, 1, 3]
def baseStart_1966224 : Nat := 118140960795 + 1966224 * 2 ^ 59
def prefixEnd_1966224 : Nat := 4983230072969 + 3 ^ 40 * 1966224 * 2
def baseEnd_1966224 : Nat := 673078657604013582171671

theorem tailTrace_1966224 : CollatzResearch.WordTrace tailWord_1966224 prefixEnd_1966224 673078657604013582171671 := by
  unfold tailWord_1966224
  simp only [CollatzResearch.WordTrace]
  refine ⟨35857040414356863584780863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47809387219142484779707817 35857040414356863584780863)
  ·
    refine ⟨53785560621535295377171295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35857040414356863584780863 53785560621535295377171295)
    ·
      refine ⟨80678340932302943065756943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53785560621535295377171295 80678340932302943065756943)
      ·
        refine ⟨121017511398454414598635415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80678340932302943065756943 121017511398454414598635415)
        ·
          refine ⟨181526267097681621897953123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121017511398454414598635415 181526267097681621897953123)
          ·
            refine ⟨272289400646522432846929685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181526267097681621897953123 272289400646522432846929685)
            ·
              refine ⟨12763565655305739039699829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 272289400646522432846929685 12763565655305739039699829)
              ·
                refine ⟨1196584280184913034971859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12763565655305739039699829 1196584280184913034971859)
                ·
                  refine ⟨1794876420277369552457789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196584280184913034971859 1794876420277369552457789)
                  ·
                    refine ⟨673078657604013582171671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1794876420277369552457789 673078657604013582171671)
                    ·
                      rfl

theorem cell22_1966224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 1, 3].length) (baseStart_1966224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966224 prefixEnd_1966224 := by exact prefixLift 1966224
  have htrace : WordTrace (prefixWord ++ tailWord_1966224) baseStart_1966224 baseEnd_1966224 := by
    simpa [prefixWord, tailWord_1966224, baseEnd_1966224] using wordTrace_append hprefix tailTrace_1966224
  have hstable : (prefixWord ++ tailWord_1966224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966224).length < 2 ^ (prefixWord ++ tailWord_1966224).sum := by decide
  have hdescent : baseEnd_1966224 < baseStart_1966224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966237 : List Nat := [1, 4, 2, 1, 1, 3, 1, 4, 5]
def baseStart_1966237 : Nat := 118140960795 + 1966237 * 2 ^ 59
def prefixEnd_1966237 : Nat := 4983230072969 + 3 ^ 40 * 1966237 * 2
def baseEnd_1966237 : Nat := 224361035923228627198877

theorem tailTrace_1966237 : CollatzResearch.WordTrace tailWord_1966237 prefixEnd_1966237 224361035923228627198877 := by
  unfold tailWord_1966237
  simp only [CollatzResearch.WordTrace]
  refine ⟨71714554977666630389784965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47809703318444420259856643 71714554977666630389784965)
  ·
    refine ⟨13446479058312493198084681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71714554977666630389784965 13446479058312493198084681)
    ·
      refine ⟨10084859293734369898563511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13446479058312493198084681 10084859293734369898563511)
      ·
        refine ⟨15127288940601554847845267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10084859293734369898563511 15127288940601554847845267)
        ·
          refine ⟨22690933410902332271767901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15127288940601554847845267 22690933410902332271767901)
          ·
            refine ⟨8509100029088374601912963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22690933410902332271767901 8509100029088374601912963)
            ·
              refine ⟨12763650043632561902869445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8509100029088374601912963 12763650043632561902869445)
              ·
                refine ⟨2393184383181105356788021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12763650043632561902869445 2393184383181105356788021)
                ·
                  refine ⟨224361035923228627198877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2393184383181105356788021 224361035923228627198877)
                  ·
                    rfl

theorem cell22_1966237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_1966237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966237 prefixEnd_1966237 := by exact prefixLift 1966237
  have htrace : WordTrace (prefixWord ++ tailWord_1966237) baseStart_1966237 baseEnd_1966237 := by
    simpa [prefixWord, tailWord_1966237, baseEnd_1966237] using wordTrace_append hprefix tailTrace_1966237
  have hstable : (prefixWord ++ tailWord_1966237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966237).length < 2 ^ (prefixWord ++ tailWord_1966237).sum := by decide
  have hdescent : baseEnd_1966237 < baseStart_1966237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966241 : List Nat := [1, 2, 3, 3, 1, 3, 1, 4, 1, 3]
def baseStart_1966241 : Nat := 118140960795 + 1966241 * 2 ^ 59
def prefixEnd_1966241 : Nat := 4983230072969 + 3 ^ 40 * 1966241 * 2
def baseEnd_1966241 : Nat := 673084477051431204496619

theorem tailTrace_1966241 : CollatzResearch.WordTrace tailWord_1966241 prefixEnd_1966241 673084477051431204496619 := by
  unfold tailWord_1966241
  simp only [CollatzResearch.WordTrace]
  refine ⟨71714700869652139072930577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47809800579768092715287051 71714700869652139072930577)
  ·
    refine ⟨53786025652239104304697933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71714700869652139072930577 53786025652239104304697933)
    ·
      refine ⟨20169759619589664114261725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53786025652239104304697933 20169759619589664114261725)
      ·
        refine ⟨7563659857346124042848147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20169759619589664114261725 7563659857346124042848147)
        ·
          refine ⟨11345489786019186064272221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7563659857346124042848147 11345489786019186064272221)
          ·
            refine ⟨4254558669757194774102083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11345489786019186064272221 4254558669757194774102083)
            ·
              refine ⟨6381838004635792161153125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4254558669757194774102083 6381838004635792161153125)
              ·
                refine ⟨1196594625869211030216211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6381838004635792161153125 1196594625869211030216211)
                ·
                  refine ⟨1794891938803816545324317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196594625869211030216211 1794891938803816545324317)
                  ·
                    refine ⟨673084477051431204496619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1794891938803816545324317 673084477051431204496619)
                    ·
                      rfl

theorem cell22_1966241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_1966241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966241 prefixEnd_1966241 := by exact prefixLift 1966241
  have htrace : WordTrace (prefixWord ++ tailWord_1966241) baseStart_1966241 baseEnd_1966241 := by
    simpa [prefixWord, tailWord_1966241, baseEnd_1966241] using wordTrace_append hprefix tailTrace_1966241
  have hstable : (prefixWord ++ tailWord_1966241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966241).length < 2 ^ (prefixWord ++ tailWord_1966241).sum := by decide
  have hdescent : baseEnd_1966241 < baseStart_1966241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966267 : List Nat := [1, 1, 1, 1, 1, 2, 6, 4, 1, 4]
def baseStart_1966267 : Nat := 118140960795 + 1966267 * 2 ^ 59
def prefixEnd_1966267 : Nat := 4983230072969 + 3 ^ 40 * 1966267 * 2
def baseEnd_1966267 : Nat := 673093377382775803346539

theorem tailTrace_1966267 : CollatzResearch.WordTrace tailWord_1966267 prefixEnd_1966267 673093377382775803346539 := by
  unfold tailWord_1966267
  simp only [CollatzResearch.WordTrace]
  refine ⟨71715649167557945513377055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47810432778371963675584703 71715649167557945513377055)
  ·
    refine ⟨107573473751336918270065583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71715649167557945513377055 107573473751336918270065583)
    ·
      refine ⟨161360210627005377405098375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107573473751336918270065583 161360210627005377405098375)
      ·
        refine ⟨242040315940508066107647563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161360210627005377405098375 242040315940508066107647563)
        ·
          refine ⟨363060473910762099161471345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242040315940508066107647563 363060473910762099161471345)
          ·
            refine ⟨272295355433071574371103509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 363060473910762099161471345 272295355433071574371103509)
            ·
              refine ⟨12763844785925230048645477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 272295355433071574371103509 12763844785925230048645477)
              ·
                refine ⟨2393220897360980634121027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12763844785925230048645477 2393220897360980634121027)
                ·
                  refine ⟨3589831346041470951181541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393220897360980634121027 3589831346041470951181541)
                  ·
                    refine ⟨673093377382775803346539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3589831346041470951181541 673093377382775803346539)
                    ·
                      rfl

theorem cell22_1966267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 4].length) (baseStart_1966267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966267 prefixEnd_1966267 := by exact prefixLift 1966267
  have htrace : WordTrace (prefixWord ++ tailWord_1966267) baseStart_1966267 baseEnd_1966267 := by
    simpa [prefixWord, tailWord_1966267, baseEnd_1966267] using wordTrace_append hprefix tailTrace_1966267
  have hstable : (prefixWord ++ tailWord_1966267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966267).length < 2 ^ (prefixWord ++ tailWord_1966267).sum := by decide
  have hdescent : baseEnd_1966267 < baseStart_1966267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966312 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 1, 6]
def baseStart_1966312 : Nat := 118140960795 + 1966312 * 2 ^ 59
def prefixEnd_1966312 : Nat := 4983230072969 + 3 ^ 40 * 1966312 * 2
def baseEnd_1966312 : Nat := 673108781802410685971401

theorem tailTrace_1966312 : CollatzResearch.WordTrace tailWord_1966312 prefixEnd_1966312 673108781802410685971401 := by
  unfold tailWord_1966312
  simp only [CollatzResearch.WordTrace]
  refine ⟨35858645226197459099382595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47811526968263278799176793 35858645226197459099382595)
  ·
    refine ⟨53787967839296188649073893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35858645226197459099382595 53787967839296188649073893)
    ·
      refine ⟨10085243969868035371701355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53787967839296188649073893 10085243969868035371701355)
      ·
        refine ⟨15127865954802053057552033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10085243969868035371701355 15127865954802053057552033)
        ·
          refine ⟨11345899466101539793164025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15127865954802053057552033 11345899466101539793164025)
          ·
            refine ⟨8509424599576154844873019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11345899466101539793164025 8509424599576154844873019)
            ·
              refine ⟨12764136899364232267309529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8509424599576154844873019 12764136899364232267309529)
              ·
                refine ⟨9573102674523174200482147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12764136899364232267309529 9573102674523174200482147)
                ·
                  refine ⟨14359654011784761300723221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9573102674523174200482147 14359654011784761300723221)
                  ·
                    refine ⟨673108781802410685971401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14359654011784761300723221 673108781802410685971401)
                    ·
                      rfl

theorem cell22_1966312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_1966312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966312 prefixEnd_1966312 := by exact prefixLift 1966312
  have htrace : WordTrace (prefixWord ++ tailWord_1966312) baseStart_1966312 baseEnd_1966312 := by
    simpa [prefixWord, tailWord_1966312, baseEnd_1966312] using wordTrace_append hprefix tailTrace_1966312
  have hstable : (prefixWord ++ tailWord_1966312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966312).length < 2 ^ (prefixWord ++ tailWord_1966312).sum := by decide
  have hdescent : baseEnd_1966312 < baseStart_1966312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966365 : List Nat := [1, 4, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_1966365 : Nat := 118140960795 + 1966365 * 2 ^ 59
def prefixEnd_1966365 : Nat := 4983230072969 + 3 ^ 40 * 1966365 * 2
def baseEnd_1966365 : Nat := 673126924785536214396239

theorem tailTrace_1966365 : CollatzResearch.WordTrace tailWord_1966365 prefixEnd_1966365 673126924785536214396239 := by
  unfold tailWord_1966365
  simp only [CollatzResearch.WordTrace]
  refine ⟨71719223521202908250444549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47812815680801938833629699 71719223521202908250444549)
  ·
    refine ⟨13447354410225545296958353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71719223521202908250444549 13447354410225545296958353)
    ·
      refine ⟨10085515807669158972718765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13447354410225545296958353 10085515807669158972718765)
      ·
        refine ⟨3782068427875934614769537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10085515807669158972718765 3782068427875934614769537)
        ·
          refine ⟨2836551320906950961077153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3782068427875934614769537 2836551320906950961077153)
          ·
            refine ⟨2127413490680213220807865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2836551320906950961077153 2127413490680213220807865)
            ·
              refine ⟨1595560118010159915605899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2127413490680213220807865 1595560118010159915605899)
              ·
                refine ⟨2393340177015239873408849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595560118010159915605899 2393340177015239873408849)
                ·
                  refine ⟨1795005132761429905056637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2393340177015239873408849 1795005132761429905056637)
                  ·
                    refine ⟨673126924785536214396239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1795005132761429905056637 673126924785536214396239)
                    ·
                      rfl

theorem cell22_1966365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_1966365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966365 prefixEnd_1966365 := by exact prefixLift 1966365
  have htrace : WordTrace (prefixWord ++ tailWord_1966365) baseStart_1966365 baseEnd_1966365 := by
    simpa [prefixWord, tailWord_1966365, baseEnd_1966365] using wordTrace_append hprefix tailTrace_1966365
  have hstable : (prefixWord ++ tailWord_1966365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966365).length < 2 ^ (prefixWord ++ tailWord_1966365).sum := by decide
  have hdescent : baseEnd_1966365 < baseStart_1966365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966434 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 8]
def baseStart_1966434 : Nat := 118140960795 + 1966434 * 2 ^ 59
def prefixEnd_1966434 : Nat := 4983230072969 + 3 ^ 40 * 1966434 * 2
def baseEnd_1966434 : Nat := 224383514965214344807009

theorem tailTrace_1966434 : CollatzResearch.WordTrace tailWord_1966434 prefixEnd_1966434 224383514965214344807009 := by
  unfold tailWord_1966434
  simp only [CollatzResearch.WordTrace]
  refine ⟨17930435039488233258676589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47814493438635288689804237 17930435039488233258676589)
  ·
    refine ⟨6723913139808087472003721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17930435039488233258676589 6723913139808087472003721)
    ·
      refine ⟨5042934854856065604002791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6723913139808087472003721 5042934854856065604002791)
      ·
        refine ⟨7564402282284098406004187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5042934854856065604002791 7564402282284098406004187)
        ·
          refine ⟨11346603423426147609006281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7564402282284098406004187 11346603423426147609006281)
          ·
            refine ⟨8509952567569610706754711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11346603423426147609006281 8509952567569610706754711)
            ·
              refine ⟨12764928851354416060132067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8509952567569610706754711 12764928851354416060132067)
              ·
                refine ⟨19147393277031624090198101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12764928851354416060132067 19147393277031624090198101)
                ·
                  refine ⟨224383514965214344807009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19147393277031624090198101 224383514965214344807009)
                  ·
                    rfl

theorem cell22_1966434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_1966434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966434 prefixEnd_1966434 := by exact prefixLift 1966434
  have htrace : WordTrace (prefixWord ++ tailWord_1966434) baseStart_1966434 baseEnd_1966434 := by
    simpa [prefixWord, tailWord_1966434, baseEnd_1966434] using wordTrace_append hprefix tailTrace_1966434
  have hstable : (prefixWord ++ tailWord_1966434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966434).length < 2 ^ (prefixWord ++ tailWord_1966434).sum := by decide
  have hdescent : baseEnd_1966434 < baseStart_1966434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966449 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 4, 3]
def baseStart_1966449 : Nat := 118140960795 + 1966449 * 2 ^ 59
def prefixEnd_1966449 : Nat := 4983230072969 + 3 ^ 40 * 1966449 * 2
def baseEnd_1966449 : Nat := 673155679702187995295981

theorem tailTrace_1966449 : CollatzResearch.WordTrace tailWord_1966449 prefixEnd_1966449 673155679702187995295981 := by
  unfold tailWord_1966449
  simp only [CollatzResearch.WordTrace]
  refine ⟨71722287252898590596502401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47814858168599060397668267 71722287252898590596502401)
  ·
    refine ⟨53791715439673942947376801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71722287252898590596502401 53791715439673942947376801)
    ·
      refine ⟨40343786579755457210532601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53791715439673942947376801 40343786579755457210532601)
      ·
        refine ⟨30257839934816592907899451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40343786579755457210532601 30257839934816592907899451)
        ·
          refine ⟨45386759902224889361849177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30257839934816592907899451 45386759902224889361849177)
          ·
            refine ⟨34040069926668667021386883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45386759902224889361849177 34040069926668667021386883)
            ·
              refine ⟨51060104890003000532080325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34040069926668667021386883 51060104890003000532080325)
              ·
                refine ⟨9573769666875562599765061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51060104890003000532080325 9573769666875562599765061)
                ·
                  refine ⟨1795081812539167987455949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9573769666875562599765061 1795081812539167987455949)
                  ·
                    refine ⟨673155679702187995295981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1795081812539167987455949 673155679702187995295981)
                    ·
                      rfl

theorem cell22_1966449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_1966449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966449 prefixEnd_1966449 := by exact prefixLift 1966449
  have htrace : WordTrace (prefixWord ++ tailWord_1966449) baseStart_1966449 baseEnd_1966449 := by
    simpa [prefixWord, tailWord_1966449, baseEnd_1966449] using wordTrace_append hprefix tailTrace_1966449
  have hstable : (prefixWord ++ tailWord_1966449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966449).length < 2 ^ (prefixWord ++ tailWord_1966449).sum := by decide
  have hdescent : baseEnd_1966449 < baseStart_1966449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966453 : List Nat := [1, 3, 4, 1, 2, 1, 4, 1, 1, 4]
def baseStart_1966453 : Nat := 118140960795 + 1966453 * 2 ^ 59
def prefixEnd_1966453 : Nat := 4983230072969 + 3 ^ 40 * 1966453 * 2
def baseEnd_1966453 : Nat := 673157048983933318195969

theorem tailTrace_1966453 : CollatzResearch.WordTrace tailWord_1966453 prefixEnd_1966453 673157048983933318195969 := by
  unfold tailWord_1966453
  simp only [CollatzResearch.WordTrace]
  refine ⟨71722433144884099279648013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47814955429922732853098675 71722433144884099279648013)
  ·
    refine ⟨26895912429331537229868005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71722433144884099279648013 26895912429331537229868005)
    ·
      refine ⟨5042983580499663230600251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26895912429331537229868005 5042983580499663230600251)
      ·
        refine ⟨7564475370749494845900377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5042983580499663230600251 7564475370749494845900377)
        ·
          refine ⟨5673356528062121134425283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7564475370749494845900377 5673356528062121134425283)
          ·
            refine ⟨8510034792093181701637925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5673356528062121134425283 8510034792093181701637925)
            ·
              refine ⟨1595631523517471569057111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8510034792093181701637925 1595631523517471569057111)
              ·
                refine ⟨2393447285276207353585667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1595631523517471569057111 2393447285276207353585667)
                ·
                  refine ⟨3590170927914311030378501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393447285276207353585667 3590170927914311030378501)
                  ·
                    refine ⟨673157048983933318195969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3590170927914311030378501 673157048983933318195969)
                    ·
                      rfl

theorem cell22_1966453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_1966453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966453 prefixEnd_1966453 := by exact prefixLift 1966453
  have htrace : WordTrace (prefixWord ++ tailWord_1966453) baseStart_1966453 baseEnd_1966453 := by
    simpa [prefixWord, tailWord_1966453, baseEnd_1966453] using wordTrace_append hprefix tailTrace_1966453
  have hstable : (prefixWord ++ tailWord_1966453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966453).length < 2 ^ (prefixWord ++ tailWord_1966453).sum := by decide
  have hdescent : baseEnd_1966453 < baseStart_1966453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966496 : List Nat := [2, 1, 1, 4, 1, 5, 2, 6]
def baseStart_1966496 : Nat := 118140960795 + 1966496 * 2 ^ 59
def prefixEnd_1966496 : Nat := 4983230072969 + 3 ^ 40 * 1966496 * 2
def baseEnd_1966496 : Nat := 74796863195855059930093

theorem tailTrace_1966496 : CollatzResearch.WordTrace tailWord_1966496 prefixEnd_1966496 74796863195855059930093 := by
  unfold tailWord_1966496
  simp only [CollatzResearch.WordTrace]
  refine ⟨35862000741864158811731671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47816000989152211748975561 35862000741864158811731671)
  ·
    refine ⟨53793001112796238217597507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35862000741864158811731671 53793001112796238217597507)
    ·
      refine ⟨80689501669194357326396261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53793001112796238217597507 80689501669194357326396261)
      ·
        refine ⟨15129281562973941998699299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80689501669194357326396261 15129281562973941998699299)
        ·
          refine ⟨22693922344460912998048949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15129281562973941998699299 22693922344460912998048949)
          ·
            refine ⟨2127555219793210593567089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22693922344460912998048949 2127555219793210593567089)
            ·
              refine ⟨1595666414844907945175317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2127555219793210593567089 1595666414844907945175317)
              ·
                refine ⟨74796863195855059930093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1595666414844907945175317 74796863195855059930093)
                ·
                  rfl

theorem cell22_1966496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 6].length) (baseStart_1966496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966496 prefixEnd_1966496 := by exact prefixLift 1966496
  have htrace : WordTrace (prefixWord ++ tailWord_1966496) baseStart_1966496 baseEnd_1966496 := by
    simpa [prefixWord, tailWord_1966496, baseEnd_1966496] using wordTrace_append hprefix tailTrace_1966496
  have hstable : (prefixWord ++ tailWord_1966496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966496).length < 2 ^ (prefixWord ++ tailWord_1966496).sum := by decide
  have hdescent : baseEnd_1966496 < baseStart_1966496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966584 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 3, 5]
def baseStart_1966584 : Nat := 118140960795 + 1966584 * 2 ^ 59
def prefixEnd_1966584 : Nat := 4983230072969 + 3 ^ 40 * 1966584 * 2
def baseEnd_1966584 : Nat := 673201892961092643170567

theorem tailTrace_1966584 : CollatzResearch.WordTrace tailWord_1966584 prefixEnd_1966584 673201892961092643170567 := by
  unfold tailWord_1966584
  simp only [CollatzResearch.WordTrace]
  refine ⟨35863605553704754326333403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47818140738273005768444537 35863605553704754326333403)
  ·
    refine ⟨53795408330557131489500105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35863605553704754326333403 53795408330557131489500105)
    ·
      refine ⟨40346556247917848617125079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53795408330557131489500105 40346556247917848617125079)
      ·
        refine ⟨60519834371876772925687619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40346556247917848617125079 60519834371876772925687619)
        ·
          refine ⟨90779751557815159388531429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60519834371876772925687619 90779751557815159388531429)
          ·
            refine ⟨17021203417090342385349643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90779751557815159388531429 17021203417090342385349643)
            ·
              refine ⟨25531805125635513578024465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17021203417090342385349643 25531805125635513578024465)
              ·
                refine ⟨19148853844226635183518349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25531805125635513578024465 19148853844226635183518349)
                ·
                  refine ⟨7180820191584988193819381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19148853844226635183518349 7180820191584988193819381)
                  ·
                    refine ⟨673201892961092643170567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7180820191584988193819381 673201892961092643170567)
                    ·
                      rfl

theorem cell22_1966584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_1966584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966584 prefixEnd_1966584 := by exact prefixLift 1966584
  have htrace : WordTrace (prefixWord ++ tailWord_1966584) baseStart_1966584 baseEnd_1966584 := by
    simpa [prefixWord, tailWord_1966584, baseEnd_1966584] using wordTrace_append hprefix tailTrace_1966584
  have hstable : (prefixWord ++ tailWord_1966584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966584).length < 2 ^ (prefixWord ++ tailWord_1966584).sum := by decide
  have hdescent : baseEnd_1966584 < baseStart_1966584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966605 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1966605 : Nat := 118140960795 + 1966605 * 2 ^ 59
def prefixEnd_1966605 : Nat := 4983230072969 + 3 ^ 40 * 1966605 * 2
def baseEnd_1966605 : Nat := 673209081690255588395503

theorem tailTrace_1966605 : CollatzResearch.WordTrace tailWord_1966605 prefixEnd_1966605 673209081690255588395503 := by
  unfold tailWord_1966605
  simp only [CollatzResearch.WordTrace]
  refine ⟨71727977040333429239181269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47818651360222286159454179 71727977040333429239181269)
  ·
    refine ⟨1681124461882814747793311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 71727977040333429239181269 1681124461882814747793311)
    ·
      refine ⟨2521686692824222121689967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1681124461882814747793311 2521686692824222121689967)
      ·
        refine ⟨3782530039236333182534951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2521686692824222121689967 3782530039236333182534951)
        ·
          refine ⟨5673795058854499773802427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3782530039236333182534951 5673795058854499773802427)
          ·
            refine ⟨8510692588281749660703641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5673795058854499773802427 8510692588281749660703641)
            ·
              refine ⟨6383019441211312245527731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8510692588281749660703641 6383019441211312245527731)
              ·
                refine ⟨9574529161816968368291597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383019441211312245527731 9574529161816968368291597)
                ·
                  refine ⟨3590448435681363138109349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9574529161816968368291597 3590448435681363138109349)
                  ·
                    refine ⟨673209081690255588395503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3590448435681363138109349 673209081690255588395503)
                    ·
                      rfl

theorem cell22_1966605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1966605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966605 prefixEnd_1966605 := by exact prefixLift 1966605
  have htrace : WordTrace (prefixWord ++ tailWord_1966605) baseStart_1966605 baseEnd_1966605 := by
    simpa [prefixWord, tailWord_1966605, baseEnd_1966605] using wordTrace_append hprefix tailTrace_1966605
  have hstable : (prefixWord ++ tailWord_1966605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966605).length < 2 ^ (prefixWord ++ tailWord_1966605).sum := by decide
  have hdescent : baseEnd_1966605 < baseStart_1966605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966616 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 1, 6]
def baseStart_1966616 : Nat := 118140960795 + 1966616 * 2 ^ 59
def prefixEnd_1966616 : Nat := 4983230072969 + 3 ^ 40 * 1966616 * 2
def baseEnd_1966616 : Nat := 673212847215055226370469

theorem tailTrace_1966616 : CollatzResearch.WordTrace tailWord_1966616 prefixEnd_1966616 673212847215055226370469 := by
  unfold tailWord_1966616
  simp only [CollatzResearch.WordTrace]
  refine ⟨35864189121646789058915851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47818918828862385411887801 35864189121646789058915851)
  ·
    refine ⟨53796283682470183588373777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35864189121646789058915851 53796283682470183588373777)
    ·
      refine ⟨40347212761852637691280333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53796283682470183588373777 40347212761852637691280333)
      ·
        refine ⟨15130204785694739134230125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40347212761852637691280333 15130204785694739134230125)
        ·
          refine ⟨5673826794635527175336297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15130204785694739134230125 5673826794635527175336297)
          ·
            refine ⟨4255370095976645381502223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5673826794635527175336297 4255370095976645381502223)
            ·
              refine ⟨6383055143964968072253335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4255370095976645381502223 6383055143964968072253335)
              ·
                refine ⟨9574582715947452108380003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6383055143964968072253335 9574582715947452108380003)
                ·
                  refine ⟨14361874073921178162570005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9574582715947452108380003 14361874073921178162570005)
                  ·
                    refine ⟨673212847215055226370469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14361874073921178162570005 673212847215055226370469)
                    ·
                      rfl

theorem cell22_1966616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_1966616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966616 prefixEnd_1966616 := by exact prefixLift 1966616
  have htrace : WordTrace (prefixWord ++ tailWord_1966616) baseStart_1966616 baseEnd_1966616 := by
    simpa [prefixWord, tailWord_1966616, baseEnd_1966616] using wordTrace_append hprefix tailTrace_1966616
  have hstable : (prefixWord ++ tailWord_1966616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966616).length < 2 ^ (prefixWord ++ tailWord_1966616).sum := by decide
  have hdescent : baseEnd_1966616 < baseStart_1966616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966637 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 6]
def baseStart_1966637 : Nat := 118140960795 + 1966637 * 2 ^ 59
def prefixEnd_1966637 : Nat := 4983230072969 + 3 ^ 40 * 1966637 * 2
def baseEnd_1966637 : Nat := 224406678648072723865135

theorem tailTrace_1966637 : CollatzResearch.WordTrace tailWord_1966637 prefixEnd_1966637 224406678648072723865135 := by
  unfold tailWord_1966637
  simp only [CollatzResearch.WordTrace]
  refine ⟨71729144176217498704346165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47819429450811665802897443 71729144176217498704346165)
  ·
    refine ⟨6724607266520390503532453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71729144176217498704346165 6724607266520390503532453)
    ·
      refine ⟨1260863862472573219412335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6724607266520390503532453 1260863862472573219412335)
      ·
        refine ⟨1891295793708859829118503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1260863862472573219412335 1891295793708859829118503)
        ·
          refine ⟨2836943690563289743677755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1891295793708859829118503 2836943690563289743677755)
          ·
            refine ⟨4255415535844934615516633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2836943690563289743677755 4255415535844934615516633)
            ·
              refine ⟨3191561651883700961637475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4255415535844934615516633 3191561651883700961637475)
              ·
                refine ⟨4787342477825551442456213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191561651883700961637475 4787342477825551442456213)
                ·
                  refine ⟨224406678648072723865135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4787342477825551442456213 224406678648072723865135)
                  ·
                    rfl

theorem cell22_1966637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_1966637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966637 prefixEnd_1966637 := by exact prefixLift 1966637
  have htrace : WordTrace (prefixWord ++ tailWord_1966637) baseStart_1966637 baseEnd_1966637 := by
    simpa [prefixWord, tailWord_1966637, baseEnd_1966637] using wordTrace_append hprefix tailTrace_1966637
  have hstable : (prefixWord ++ tailWord_1966637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966637).length < 2 ^ (prefixWord ++ tailWord_1966637).sum := by decide
  have hdescent : baseEnd_1966637 < baseStart_1966637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966663 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 3, 3]
def baseStart_1966663 : Nat := 118140960795 + 1966663 * 2 ^ 59
def prefixEnd_1966663 : Nat := 4983230072969 + 3 ^ 40 * 1966663 * 2
def baseEnd_1966663 : Nat := 673228936275562770445325

theorem tailTrace_1966663 : CollatzResearch.WordTrace tailWord_1966663 prefixEnd_1966663 673228936275562770445325 := by
  unfold tailWord_1966663
  simp only [CollatzResearch.WordTrace]
  refine ⟨71730092474123305144792643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47820061649415536763195095 71730092474123305144792643)
  ·
    refine ⟨107595138711184957717188965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71730092474123305144792643 107595138711184957717188965)
    ·
      refine ⟨20174088508347179571972931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107595138711184957717188965 20174088508347179571972931)
      ·
        refine ⟨30261132762520769357959397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20174088508347179571972931 30261132762520769357959397)
        ·
          refine ⟨5673962392972644254617387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30261132762520769357959397 5673962392972644254617387)
          ·
            refine ⟨8510943589458966381926081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5673962392972644254617387 8510943589458966381926081)
            ·
              refine ⟨6383207692094224786444561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8510943589458966381926081 6383207692094224786444561)
              ·
                refine ⟨4787405769070668589833421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6383207692094224786444561 4787405769070668589833421)
                ·
                  refine ⟨1795277163401500721187533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4787405769070668589833421 1795277163401500721187533)
                  ·
                    refine ⟨673228936275562770445325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1795277163401500721187533 673228936275562770445325)
                    ·
                      rfl

theorem cell22_1966663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_1966663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966663 prefixEnd_1966663 := by exact prefixLift 1966663
  have htrace : WordTrace (prefixWord ++ tailWord_1966663) baseStart_1966663 baseEnd_1966663 := by
    simpa [prefixWord, tailWord_1966663, baseEnd_1966663] using wordTrace_append hprefix tailTrace_1966663
  have hstable : (prefixWord ++ tailWord_1966663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966663).length < 2 ^ (prefixWord ++ tailWord_1966663).sum := by decide
  have hdescent : baseEnd_1966663 < baseStart_1966663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966676 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 7]
def baseStart_1966676 : Nat := 118140960795 + 1966676 * 2 ^ 59
def prefixEnd_1966676 : Nat := 4983230072969 + 3 ^ 40 * 1966676 * 2
def baseEnd_1966676 : Nat := 224411128813745023290095

theorem tailTrace_1966676 : CollatzResearch.WordTrace tailWord_1966676 prefixEnd_1966676 224411128813745023290095 := by
  unfold tailWord_1966676
  simp only [CollatzResearch.WordTrace]
  refine ⟨35865283311538104182507941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47820377748717472243343921 35865283311538104182507941)
  ·
    refine ⟨6724740620913394534220239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35865283311538104182507941 6724740620913394534220239)
    ·
      refine ⟨10087110931370091801330359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6724740620913394534220239 10087110931370091801330359)
      ·
        refine ⟨15130666397055137701995539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10087110931370091801330359 15130666397055137701995539)
        ·
          refine ⟨22695999595582706552993309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15130666397055137701995539 22695999595582706552993309)
          ·
            refine ⟨8510999848343514957372491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22695999595582706552993309 8510999848343514957372491)
            ·
              refine ⟨12766499772515272436058737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8510999848343514957372491 12766499772515272436058737)
              ·
                refine ⟨9574874829386454327044053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12766499772515272436058737 9574874829386454327044053)
                ·
                  refine ⟨224411128813745023290095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9574874829386454327044053 224411128813745023290095)
                  ·
                    rfl

theorem cell22_1966676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_1966676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966676 prefixEnd_1966676 := by exact prefixLift 1966676
  have htrace : WordTrace (prefixWord ++ tailWord_1966676) baseStart_1966676 baseEnd_1966676 := by
    simpa [prefixWord, tailWord_1966676, baseEnd_1966676] using wordTrace_append hprefix tailTrace_1966676
  have hstable : (prefixWord ++ tailWord_1966676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966676).length < 2 ^ (prefixWord ++ tailWord_1966676).sum := by decide
  have hdescent : baseEnd_1966676 < baseStart_1966676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966680 : List Nat := [2, 1, 2, 2, 1, 2, 5, 3, 1, 3]
def baseStart_1966680 : Nat := 118140960795 + 1966680 * 2 ^ 59
def prefixEnd_1966680 : Nat := 4983230072969 + 3 ^ 40 * 1966680 * 2
def baseEnd_1966680 : Nat := 673234755722980392770273

theorem tailTrace_1966680 : CollatzResearch.WordTrace tailWord_1966680 prefixEnd_1966680 673234755722980392770273 := by
  unfold tailWord_1966680
  simp only [CollatzResearch.WordTrace]
  refine ⟨35865356257530858524080747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47820475010041144698774329 35865356257530858524080747)
  ·
    refine ⟨53798034386296287786121121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35865356257530858524080747 53798034386296287786121121)
    ·
      refine ⟨40348525789722215839590841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53798034386296287786121121 40348525789722215839590841)
      ·
        refine ⟨30261394342291661879693131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40348525789722215839590841 30261394342291661879693131)
        ·
          refine ⟨45392091513437492819539697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30261394342291661879693131 45392091513437492819539697)
          ·
            refine ⟨34044068635078119614654773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45392091513437492819539697 34044068635078119614654773)
            ·
              refine ⟨3191631434538573713873885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34044068635078119614654773 3191631434538573713873885)
              ·
                refine ⟨1196861787951965142702707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3191631434538573713873885 1196861787951965142702707)
                ·
                  refine ⟨1795292681927947714054061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1196861787951965142702707 1795292681927947714054061)
                  ·
                    refine ⟨673234755722980392770273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1795292681927947714054061 673234755722980392770273)
                    ·
                      rfl

theorem cell22_1966680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_1966680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966680 prefixEnd_1966680 := by exact prefixLift 1966680
  have htrace : WordTrace (prefixWord ++ tailWord_1966680) baseStart_1966680 baseEnd_1966680 := by
    simpa [prefixWord, tailWord_1966680, baseEnd_1966680] using wordTrace_append hprefix tailTrace_1966680
  have hstable : (prefixWord ++ tailWord_1966680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966680).length < 2 ^ (prefixWord ++ tailWord_1966680).sum := by decide
  have hdescent : baseEnd_1966680 < baseStart_1966680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966710 : List Nat := [5, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_1966710 : Nat := 118140960795 + 1966710 * 2 ^ 59
def prefixEnd_1966710 : Nat := 4983230072969 + 3 ^ 40 * 1966710 * 2
def baseEnd_1966710 : Nat := 224415008445356771506727

theorem tailTrace_1966710 : CollatzResearch.WordTrace tailWord_1966710 prefixEnd_1966710 224415008445356771506727 := by
  unfold tailWord_1966710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4483237919059564510734599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47821204469968688114502389 4483237919059564510734599)
  ·
    refine ⟨6724856878589346766101899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4483237919059564510734599 6724856878589346766101899)
    ·
      refine ⟨10087285317884020149152849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6724856878589346766101899 10087285317884020149152849)
      ·
        refine ⟨7565463988413015111864637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10087285317884020149152849 7565463988413015111864637)
        ·
          refine ⟨2837048995654880666949239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7565463988413015111864637 2837048995654880666949239)
          ·
            refine ⟨4255573493482321000423859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837048995654880666949239 4255573493482321000423859)
            ·
              refine ⟨6383360240223481500635789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4255573493482321000423859 6383360240223481500635789)
              ·
                refine ⟨2393760090083805562738421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6383360240223481500635789 2393760090083805562738421)
                ·
                  refine ⟨224415008445356771506727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2393760090083805562738421 224415008445356771506727)
                  ·
                    rfl

theorem cell22_1966710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_1966710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966710 prefixEnd_1966710 := by exact prefixLift 1966710
  have htrace : WordTrace (prefixWord ++ tailWord_1966710) baseStart_1966710 baseEnd_1966710 := by
    simpa [prefixWord, tailWord_1966710, baseEnd_1966710] using wordTrace_append hprefix tailTrace_1966710
  have hstable : (prefixWord ++ tailWord_1966710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966710).length < 2 ^ (prefixWord ++ tailWord_1966710).sum := by decide
  have hdescent : baseEnd_1966710 < baseStart_1966710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966721 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 8]
def baseStart_1966721 : Nat := 118140960795 + 1966721 * 2 ^ 59
def prefixEnd_1966721 : Nat := 4983230072969 + 3 ^ 40 * 1966721 * 2
def baseEnd_1966721 : Nat := 224416263620289984165049

theorem tailTrace_1966721 : CollatzResearch.WordTrace tailWord_1966721 prefixEnd_1966721 224416263620289984165049 := by
  unfold tailWord_1966721
  simp only [CollatzResearch.WordTrace]
  refine ⟨71732207907913181050404017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47821471938608787366936011 71732207907913181050404017)
  ·
    refine ⟨53799155930934885787803013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71732207907913181050404017 53799155930934885787803013)
    ·
      refine ⟨10087341737050291085213065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53799155930934885787803013 10087341737050291085213065)
      ·
        refine ⟨7565506302787718313909799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10087341737050291085213065 7565506302787718313909799)
        ·
          refine ⟨11348259454181577470864699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7565506302787718313909799 11348259454181577470864699)
          ·
            refine ⟨17022389181272366206297049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11348259454181577470864699 17022389181272366206297049)
            ·
              refine ⟨12766791885954274654722787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17022389181272366206297049 12766791885954274654722787)
              ·
                refine ⟨19150187828931411982084181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12766791885954274654722787 19150187828931411982084181)
                ·
                  refine ⟨224416263620289984165049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19150187828931411982084181 224416263620289984165049)
                  ·
                    rfl

theorem cell22_1966721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_1966721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966721 prefixEnd_1966721 := by exact prefixLift 1966721
  have htrace : WordTrace (prefixWord ++ tailWord_1966721) baseStart_1966721 baseEnd_1966721 := by
    simpa [prefixWord, tailWord_1966721, baseEnd_1966721] using wordTrace_append hprefix tailTrace_1966721
  have hstable : (prefixWord ++ tailWord_1966721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966721).length < 2 ^ (prefixWord ++ tailWord_1966721).sum := by decide
  have hdescent : baseEnd_1966721 < baseStart_1966721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966723 : List Nat := [1, 1, 1, 3, 3, 1, 5, 2, 1, 4]
def baseStart_1966723 : Nat := 118140960795 + 1966723 * 2 ^ 59
def prefixEnd_1966723 : Nat := 4983230072969 + 3 ^ 40 * 1966723 * 2
def baseEnd_1966723 : Nat := 673249475501742613945141

theorem tailTrace_1966723 : CollatzResearch.WordTrace tailWord_1966723 prefixEnd_1966723 673249475501742613945141 := by
  unfold tailWord_1966723
  simp only [CollatzResearch.WordTrace]
  refine ⟨71732280853905935391976823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47821520569270623594651215 71732280853905935391976823)
  ·
    refine ⟨107598421280858903087965235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71732280853905935391976823 107598421280858903087965235)
    ·
      refine ⟨161397631921288354631947853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107598421280858903087965235 161397631921288354631947853)
      ·
        refine ⟨60524111970483132986980445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161397631921288354631947853 60524111970483132986980445)
        ·
          refine ⟨22696541988931174870117667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60524111970483132986980445 22696541988931174870117667)
          ·
            refine ⟨34044812983396762305176501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22696541988931174870117667 34044812983396762305176501)
            ·
              refine ⟨3191701217193446466110297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34044812983396762305176501 3191701217193446466110297)
              ·
                refine ⟨2393775912895084849582723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3191701217193446466110297 2393775912895084849582723)
                ·
                  refine ⟨3590663869342627274374085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2393775912895084849582723 3590663869342627274374085)
                  ·
                    refine ⟨673249475501742613945141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3590663869342627274374085 673249475501742613945141)
                    ·
                      rfl

theorem cell22_1966723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 4].length) (baseStart_1966723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966723 prefixEnd_1966723 := by exact prefixLift 1966723
  have htrace : WordTrace (prefixWord ++ tailWord_1966723) baseStart_1966723 baseEnd_1966723 := by
    simpa [prefixWord, tailWord_1966723, baseEnd_1966723] using wordTrace_append hprefix tailTrace_1966723
  have hstable : (prefixWord ++ tailWord_1966723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966723).length < 2 ^ (prefixWord ++ tailWord_1966723).sum := by decide
  have hdescent : baseEnd_1966723 < baseStart_1966723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966783 : List Nat := [1, 1, 2, 2, 2, 5, 3, 6]
def baseStart_1966783 : Nat := 118140960795 + 1966783 * 2 ^ 59
def prefixEnd_1966783 : Nat := 4983230072969 + 3 ^ 40 * 1966783 * 2
def baseEnd_1966783 : Nat := 74807779414213606382773

theorem tailTrace_1966783 : CollatzResearch.WordTrace tailWord_1966783 prefixEnd_1966783 74807779414213606382773 := by
  unfold tailWord_1966783
  simp only [CollatzResearch.WordTrace]
  refine ⟨71734469233688565639161003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47822979489125710426107335 71734469233688565639161003)
  ·
    refine ⟨107601703850532848458741505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71734469233688565639161003 107601703850532848458741505)
    ·
      refine ⟨80701277887899636344056129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107601703850532848458741505 80701277887899636344056129)
      ·
        refine ⟨60525958415924727258042097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80701277887899636344056129 60525958415924727258042097)
        ·
          refine ⟨45394468811943545443531573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60525958415924727258042097 45394468811943545443531573)
          ·
            refine ⟨4255731451119707385331085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45394468811943545443531573 4255731451119707385331085)
            ·
              refine ⟨1595899294169890269499157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4255731451119707385331085 1595899294169890269499157)
              ·
                refine ⟨74807779414213606382773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1595899294169890269499157 74807779414213606382773)
                ·
                  rfl

theorem cell22_1966783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 6].length) (baseStart_1966783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966783 prefixEnd_1966783 := by exact prefixLift 1966783
  have htrace : WordTrace (prefixWord ++ tailWord_1966783) baseStart_1966783 baseEnd_1966783 := by
    simpa [prefixWord, tailWord_1966783, baseEnd_1966783] using wordTrace_append hprefix tailTrace_1966783
  have hstable : (prefixWord ++ tailWord_1966783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966783).length < 2 ^ (prefixWord ++ tailWord_1966783).sum := by decide
  have hdescent : baseEnd_1966783 < baseStart_1966783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966804 : List Nat := [2, 4, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_1966804 : Nat := 118140960795 + 1966804 * 2 ^ 59
def prefixEnd_1966804 : Nat := 4983230072969 + 3 ^ 40 * 1966804 * 2
def baseEnd_1966804 : Nat := 673277203457085402669893

theorem tailTrace_1966804 : CollatzResearch.WordTrace tailWord_1966804 prefixEnd_1966804 673277203457085402669893 := by
  unfold tailWord_1966804
  simp only [CollatzResearch.WordTrace]
  refine ⟨35867617583306243112837733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47823490111074990817116977 35867617583306243112837733)
  ·
    refine ⟨6725178296869920583657075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35867617583306243112837733 6725178296869920583657075)
    ·
      refine ⟨10087767445304880875485613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6725178296869920583657075 10087767445304880875485613)
      ·
        refine ⟨3782912791989330328307105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10087767445304880875485613 3782912791989330328307105)
        ·
          refine ⟨2837184593991997746230329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3782912791989330328307105 2837184593991997746230329)
          ·
            refine ⟨2127888445493998309672747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2837184593991997746230329 2127888445493998309672747)
            ·
              refine ⟨3191832668240997464509121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127888445493998309672747 3191832668240997464509121)
              ·
                refine ⟨2393874501180748098381841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3191832668240997464509121 2393874501180748098381841)
                ·
                  refine ⟨1795405875885561073786381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2393874501180748098381841 1795405875885561073786381)
                  ·
                    refine ⟨673277203457085402669893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1795405875885561073786381 673277203457085402669893)
                    ·
                      rfl

theorem cell22_1966804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_1966804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966804 prefixEnd_1966804 := by exact prefixLift 1966804
  have htrace : WordTrace (prefixWord ++ tailWord_1966804) baseStart_1966804 baseEnd_1966804 := by
    simpa [prefixWord, tailWord_1966804, baseEnd_1966804] using wordTrace_append hprefix tailTrace_1966804
  have hstable : (prefixWord ++ tailWord_1966804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966804).length < 2 ^ (prefixWord ++ tailWord_1966804).sum := by decide
  have hdescent : baseEnd_1966804 < baseStart_1966804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966815 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 3, 3]
def baseStart_1966815 : Nat := 118140960795 + 1966815 * 2 ^ 59
def prefixEnd_1966815 : Nat := 4983230072969 + 3 ^ 40 * 1966815 * 2
def baseEnd_1966815 : Nat := 673280968981885040644859

theorem tailTrace_1966815 : CollatzResearch.WordTrace tailWord_1966815 prefixEnd_1966815 673280968981885040644859 := by
  unfold tailWord_1966815
  simp only [CollatzResearch.WordTrace]
  refine ⟨71735636369572635104325899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47823757579715090069550599 71735636369572635104325899)
  ·
    refine ⟨107603454554358952656488849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71735636369572635104325899 107603454554358952656488849)
    ·
      refine ⟨80702590915769214492366637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107603454554358952656488849 80702590915769214492366637)
      ·
        refine ⟨30263471593413455434637489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80702590915769214492366637 30263471593413455434637489)
        ·
          refine ⟨22697603695060091575978117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30263471593413455434637489 22697603695060091575978117)
          ·
            refine ⟨4255800692823767170495897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22697603695060091575978117 4255800692823767170495897)
            ·
              refine ⟨3191850519617825377871923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4255800692823767170495897 3191850519617825377871923)
              ·
                refine ⟨4787775779426738066807885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191850519617825377871923 4787775779426738066807885)
                ·
                  refine ⟨1795415917285026775052957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4787775779426738066807885 1795415917285026775052957)
                  ·
                    refine ⟨673280968981885040644859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1795415917285026775052957 673280968981885040644859)
                    ·
                      rfl

theorem cell22_1966815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 3].length) (baseStart_1966815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966815 prefixEnd_1966815 := by exact prefixLift 1966815
  have htrace : WordTrace (prefixWord ++ tailWord_1966815) baseStart_1966815 baseEnd_1966815 := by
    simpa [prefixWord, tailWord_1966815, baseEnd_1966815] using wordTrace_append hprefix tailTrace_1966815
  have hstable : (prefixWord ++ tailWord_1966815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966815).length < 2 ^ (prefixWord ++ tailWord_1966815).sum := by decide
  have hdescent : baseEnd_1966815 < baseStart_1966815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966841 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 2, 8]
def baseStart_1966841 : Nat := 118140960795 + 1966841 * 2 ^ 59
def prefixEnd_1966841 : Nat := 4983230072969 + 3 ^ 40 * 1966841 * 2
def baseEnd_1966841 : Nat := 673289869313229639494779

theorem tailTrace_1966841 : CollatzResearch.WordTrace tailWord_1966841 prefixEnd_1966841 673289869313229639494779 := by
  unfold tailWord_1966841
  simp only [CollatzResearch.WordTrace]
  refine ⟨71736584667478441544772377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47824389778318961029848251 71736584667478441544772377)
  ·
    refine ⟨53802438500608831158579283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71736584667478441544772377 53802438500608831158579283)
    ·
      refine ⟨80703657750913246737868925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53802438500608831158579283 80703657750913246737868925)
      ·
        refine ⟨30263871656592467526700847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80703657750913246737868925 30263871656592467526700847)
        ·
          refine ⟨45395807484888701290051271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30263871656592467526700847 45395807484888701290051271)
          ·
            refine ⟨68093711227333051935076907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45395807484888701290051271 68093711227333051935076907)
            ·
              refine ⟨102140566840999577902615361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68093711227333051935076907 102140566840999577902615361)
              ·
                refine ⟨76605425130749683426961521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 102140566840999577902615361 76605425130749683426961521)
                ·
                  refine ⟨57454068848062262570221141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76605425130749683426961521 57454068848062262570221141)
                  ·
                    refine ⟨673289869313229639494779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57454068848062262570221141 673289869313229639494779)
                    ·
                      rfl

theorem cell22_1966841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_1966841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966841 prefixEnd_1966841 := by exact prefixLift 1966841
  have htrace : WordTrace (prefixWord ++ tailWord_1966841) baseStart_1966841 baseEnd_1966841 := by
    simpa [prefixWord, tailWord_1966841, baseEnd_1966841] using wordTrace_append hprefix tailTrace_1966841
  have hstable : (prefixWord ++ tailWord_1966841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966841).length < 2 ^ (prefixWord ++ tailWord_1966841).sum := by decide
  have hdescent : baseEnd_1966841 < baseStart_1966841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966866 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1966866 : Nat := 118140960795 + 1966866 * 2 ^ 59
def prefixEnd_1966866 : Nat := 4983230072969 + 3 ^ 40 * 1966866 * 2
def baseEnd_1966866 : Nat := 673298427324137907619703

theorem tailTrace_1966866 : CollatzResearch.WordTrace tailWord_1966866 prefixEnd_1966866 673298427324137907619703 := by
  unfold tailWord_1966866
  simp only [CollatzResearch.WordTrace]
  refine ⟨17934374123096967703608113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47824997661591913876288301 17934374123096967703608113)
  ·
    refine ⟨13450780592322725777706085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17934374123096967703608113 13450780592322725777706085)
    ·
      refine ⟨2522021361060511083319891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13450780592322725777706085 2522021361060511083319891)
      ·
        refine ⟨3783032041590766624979837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522021361060511083319891 3783032041590766624979837)
        ·
          refine ⟨1418637015596537484367439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3783032041590766624979837 1418637015596537484367439)
          ·
            refine ⟨2127955523394806226551159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418637015596537484367439 2127955523394806226551159)
            ·
              refine ⟨3191933285092209339826739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2127955523394806226551159 3191933285092209339826739)
              ·
                refine ⟨4787899927638314009740109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3191933285092209339826739 4787899927638314009740109)
                ·
                  refine ⟨1795462472864367753652541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4787899927638314009740109 1795462472864367753652541)
                  ·
                    refine ⟨673298427324137907619703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1795462472864367753652541 673298427324137907619703)
                    ·
                      rfl

theorem cell22_1966866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1966866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966866 prefixEnd_1966866 := by exact prefixLift 1966866
  have htrace : WordTrace (prefixWord ++ tailWord_1966866) baseStart_1966866 baseEnd_1966866 := by
    simpa [prefixWord, tailWord_1966866, baseEnd_1966866] using wordTrace_append hprefix tailTrace_1966866
  have hstable : (prefixWord ++ tailWord_1966866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966866).length < 2 ^ (prefixWord ++ tailWord_1966866).sum := by decide
  have hdescent : baseEnd_1966866 < baseStart_1966866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966909 : List Nat := [1, 4, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_1966909 : Nat := 118140960795 + 1966909 * 2 ^ 59
def prefixEnd_1966909 : Nat := 4983230072969 + 3 ^ 40 * 1966909 * 2
def baseEnd_1966909 : Nat := 673313147102900128794571

theorem tailTrace_1966909 : CollatzResearch.WordTrace tailWord_1966909 prefixEnd_1966909 673313147102900128794571 := by
  unfold tailWord_1966909
  simp only [CollatzResearch.WordTrace]
  refine ⟨71739064831232089158247781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47826043220821392772165187 71739064831232089158247781)
  ·
    refine ⟨13451074655856016717171459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71739064831232089158247781 13451074655856016717171459)
    ·
      refine ⟨20176611983784025075757189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13451074655856016717171459 20176611983784025075757189)
      ·
        refine ⟨3783114746959504701704473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20176611983784025075757189 3783114746959504701704473)
        ·
          refine ⟨2837336060219628526278355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3783114746959504701704473 2837336060219628526278355)
          ·
            refine ⟨4256004090329442789417533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2837336060219628526278355 4256004090329442789417533)
            ·
              refine ⟨1596001533873541046031575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4256004090329442789417533 1596001533873541046031575)
              ·
                refine ⟨2394002300810311569047363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596001533873541046031575 2394002300810311569047363)
                ·
                  refine ⟨3591003451215467353571045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394002300810311569047363 3591003451215467353571045)
                  ·
                    refine ⟨673313147102900128794571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3591003451215467353571045 673313147102900128794571)
                    ·
                      rfl

theorem cell22_1966909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_1966909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966909 prefixEnd_1966909 := by exact prefixLift 1966909
  have htrace : WordTrace (prefixWord ++ tailWord_1966909) baseStart_1966909 baseEnd_1966909 := by
    simpa [prefixWord, tailWord_1966909, baseEnd_1966909] using wordTrace_append hprefix tailTrace_1966909
  have hstable : (prefixWord ++ tailWord_1966909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966909).length < 2 ^ (prefixWord ++ tailWord_1966909).sum := by decide
  have hdescent : baseEnd_1966909 < baseStart_1966909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966924 : List Nat := [2, 2, 1, 3, 3, 3, 2, 2, 4]
def baseStart_1966924 : Nat := 118140960795 + 1966924 * 2 ^ 59
def prefixEnd_1966924 : Nat := 4983230072969 + 3 ^ 40 * 1966924 * 2
def baseEnd_1966924 : Nat := 224439427303148363223175

theorem tailTrace_1966924 : CollatzResearch.WordTrace tailWord_1966924 prefixEnd_1966924 224439427303148363223175 := by
  unfold tailWord_1966924
  simp only [CollatzResearch.WordTrace]
  refine ⟨35869805963088873360021913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47826407950785164480029217 35869805963088873360021913)
  ·
    refine ⟨26902354472316655020016435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35869805963088873360021913 26902354472316655020016435)
    ·
      refine ⟨40353531708474982530024653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26902354472316655020016435 40353531708474982530024653)
      ·
        refine ⟨15132574390678118448759245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40353531708474982530024653 15132574390678118448759245)
        ·
          refine ⟨5674715396504294418284717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15132574390678118448759245 5674715396504294418284717)
          ·
            refine ⟨2128018273689110406856769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5674715396504294418284717 2128018273689110406856769)
            ·
              refine ⟨1596013705266832805142577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2128018273689110406856769 1596013705266832805142577)
              ·
                refine ⟨1197010278950124603856933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1596013705266832805142577 1197010278950124603856933)
                ·
                  refine ⟨224439427303148363223175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1197010278950124603856933 224439427303148363223175)
                  ·
                    rfl

theorem cell22_1966924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_1966924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966924 prefixEnd_1966924 := by exact prefixLift 1966924
  have htrace : WordTrace (prefixWord ++ tailWord_1966924) baseStart_1966924 baseEnd_1966924 := by
    simpa [prefixWord, tailWord_1966924, baseEnd_1966924] using wordTrace_append hprefix tailTrace_1966924
  have hstable : (prefixWord ++ tailWord_1966924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966924).length < 2 ^ (prefixWord ++ tailWord_1966924).sum := by decide
  have hdescent : baseEnd_1966924 < baseStart_1966924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966935 : List Nat := [1, 1, 3, 2, 4, 3, 1, 7]
def baseStart_1966935 : Nat := 118140960795 + 1966935 * 2 ^ 59
def prefixEnd_1966935 : Nat := 4983230072969 + 3 ^ 40 * 1966935 * 2
def baseEnd_1966935 : Nat := 74813560826027191960499

theorem tailTrace_1966935 : CollatzResearch.WordTrace tailWord_1966935 prefixEnd_1966935 74813560826027191960499 := by
  unfold tailWord_1966935
  simp only [CollatzResearch.WordTrace]
  refine ⟨71740013129137895598694259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47826675419425263732462839 71740013129137895598694259)
  ·
    refine ⟨107610019693706843398041389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71740013129137895598694259 107610019693706843398041389)
    ·
      refine ⟨40353757385140066274265521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107610019693706843398041389 40353757385140066274265521)
      ·
        refine ⟨30265318038855049705699141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40353757385140066274265521 30265318038855049705699141)
        ·
          refine ⟨5674747132285321819818589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30265318038855049705699141 5674747132285321819818589)
          ·
            refine ⟨2128030174606995682431971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5674747132285321819818589 2128030174606995682431971)
            ·
              refine ⟨3192045261910493523647957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128030174606995682431971 3192045261910493523647957)
              ·
                refine ⟨74813560826027191960499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3192045261910493523647957 74813560826027191960499)
                ·
                  rfl

theorem cell22_1966935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 7].length) (baseStart_1966935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966935 prefixEnd_1966935 := by exact prefixLift 1966935
  have htrace : WordTrace (prefixWord ++ tailWord_1966935) baseStart_1966935 baseEnd_1966935 := by
    simpa [prefixWord, tailWord_1966935, baseEnd_1966935] using wordTrace_append hprefix tailTrace_1966935
  have hstable : (prefixWord ++ tailWord_1966935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966935).length < 2 ^ (prefixWord ++ tailWord_1966935).sum := by decide
  have hdescent : baseEnd_1966935 < baseStart_1966935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966984 : List Nat := [2, 1, 3, 3, 2, 1, 2, 4, 1, 3]
def baseStart_1966984 : Nat := 118140960795 + 1966984 * 2 ^ 59
def prefixEnd_1966984 : Nat := 4983230072969 + 3 ^ 40 * 1966984 * 2
def baseEnd_1966984 : Nat := 673338821135624933169341

theorem tailTrace_1966984 : CollatzResearch.WordTrace tailWord_1966984 prefixEnd_1966984 673338821135624933169341 := by
  unfold tailWord_1966984
  simp only [CollatzResearch.WordTrace]
  refine ⟨35870900152980188483614003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47827866870640251311485337 35870900152980188483614003)
  ·
    refine ⟨53806350229470282725421005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35870900152980188483614003 53806350229470282725421005)
    ·
      refine ⟨20177381336051356022032877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53806350229470282725421005 20177381336051356022032877)
      ·
        refine ⟨7566518001019258508262329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20177381336051356022032877 7566518001019258508262329)
        ·
          refine ⟨5674888500764443881196747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7566518001019258508262329 5674888500764443881196747)
          ·
            refine ⟨8512332751146665821795121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5674888500764443881196747 8512332751146665821795121)
            ·
              refine ⟨6384249563359999366346341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8512332751146665821795121 6384249563359999366346341)
              ·
                refine ⟨1197046793129999881189939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6384249563359999366346341 1197046793129999881189939)
                ·
                  refine ⟨1795570189694999821784909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197046793129999881189939 1795570189694999821784909)
                  ·
                    refine ⟨673338821135624933169341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1795570189694999821784909 673338821135624933169341)
                    ·
                      rfl

theorem cell22_1966984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_1966984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966984 prefixEnd_1966984 := by exact prefixLift 1966984
  have htrace : WordTrace (prefixWord ++ tailWord_1966984) baseStart_1966984 baseEnd_1966984 := by
    simpa [prefixWord, tailWord_1966984, baseEnd_1966984] using wordTrace_append hprefix tailTrace_1966984
  have hstable : (prefixWord ++ tailWord_1966984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966984).length < 2 ^ (prefixWord ++ tailWord_1966984).sum := by decide
  have hdescent : baseEnd_1966984 < baseStart_1966984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1966997 : List Nat := [1, 3, 2, 1, 1, 5, 3, 1, 5]
def baseStart_1966997 : Nat := 118140960795 + 1966997 * 2 ^ 59
def prefixEnd_1966997 : Nat := 4983230072969 + 3 ^ 40 * 1966997 * 2
def baseEnd_1966997 : Nat := 224447757100432410864767

theorem tailTrace_1966997 : CollatzResearch.WordTrace tailWord_1966997 prefixEnd_1966997 224447757100432410864767 := by
  unfold tailWord_1966997
  simp only [CollatzResearch.WordTrace]
  refine ⟨71742274454913280187451245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47828182969942186791634163 71742274454913280187451245)
  ·
    refine ⟨26903352920592480070294217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71742274454913280187451245 26903352920592480070294217)
    ·
      refine ⟨20177514690444360052720663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26903352920592480070294217 20177514690444360052720663)
      ·
        refine ⟨30266272035666540079080995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20177514690444360052720663 30266272035666540079080995)
        ·
          refine ⟨45399408053499810118621493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30266272035666540079080995 45399408053499810118621493)
          ·
            refine ⟨4256194505015607198620765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45399408053499810118621493 4256194505015607198620765)
            ·
              refine ⟨1596072939380852699482787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4256194505015607198620765 1596072939380852699482787)
              ·
                refine ⟨2394109409071279049224181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596072939380852699482787 2394109409071279049224181)
                ·
                  refine ⟨224447757100432410864767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2394109409071279049224181 224447757100432410864767)
                  ·
                    rfl

theorem cell22_1966997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_1966997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1966997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1966997 prefixEnd_1966997 := by exact prefixLift 1966997
  have htrace : WordTrace (prefixWord ++ tailWord_1966997) baseStart_1966997 baseEnd_1966997 := by
    simpa [prefixWord, tailWord_1966997, baseEnd_1966997] using wordTrace_append hprefix tailTrace_1966997
  have hstable : (prefixWord ++ tailWord_1966997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1966997).length < 2 ^ (prefixWord ++ tailWord_1966997).sum := by decide
  have hdescent : baseEnd_1966997 < baseStart_1966997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1966997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967057 : List Nat := [1, 2, 2, 1, 2, 1, 5, 3, 2, 3]
def baseStart_1967057 : Nat := 118140960795 + 1967057 * 2 ^ 59
def prefixEnd_1967057 : Nat := 4983230072969 + 3 ^ 40 * 1967057 * 2
def baseEnd_1967057 : Nat := 673363810527477076094117

theorem tailTrace_1967057 : CollatzResearch.WordTrace tailWord_1967057 prefixEnd_1967057 673363810527477076094117 := by
  unfold tailWord_1967057
  simp only [CollatzResearch.WordTrace]
  refine ⟨71744462834695910434635425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47829641889797273623090283 71744462834695910434635425)
  ·
    refine ⟨53808347126021932825976569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71744462834695910434635425 53808347126021932825976569)
    ·
      refine ⟨40356260344516449619482427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53808347126021932825976569 40356260344516449619482427)
      ·
        refine ⟨60534390516774674429223641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40356260344516449619482427 60534390516774674429223641)
        ·
          refine ⟨45400792887581005821917731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60534390516774674429223641 45400792887581005821917731)
          ·
            refine ⟨68101189331371508732876597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45400792887581005821917731 68101189331371508732876597)
            ·
              refine ⟨6384486499816078943707181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68101189331371508732876597 6384486499816078943707181)
              ·
                refine ⟨2394182437431029603890193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6384486499816078943707181 2394182437431029603890193)
                ·
                  refine ⟨1795636828073272202917645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2394182437431029603890193 1795636828073272202917645)
                  ·
                    refine ⟨673363810527477076094117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1795636828073272202917645 673363810527477076094117)
                    ·
                      rfl

theorem cell22_1967057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_1967057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967057 prefixEnd_1967057 := by exact prefixLift 1967057
  have htrace : WordTrace (prefixWord ++ tailWord_1967057) baseStart_1967057 baseEnd_1967057 := by
    simpa [prefixWord, tailWord_1967057, baseEnd_1967057] using wordTrace_append hprefix tailTrace_1967057
  have hstable : (prefixWord ++ tailWord_1967057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967057).length < 2 ^ (prefixWord ++ tailWord_1967057).sum := by decide
  have hdescent : baseEnd_1967057 < baseStart_1967057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967061 : List Nat := [1, 3, 2, 3, 4, 1, 1, 2, 1, 4]
def baseStart_1967061 : Nat := 118140960795 + 1967061 * 2 ^ 59
def prefixEnd_1967061 : Nat := 4983230072969 + 3 ^ 40 * 1967061 * 2
def baseEnd_1967061 : Nat := 673365179809222398994105

theorem tailTrace_1967061 : CollatzResearch.WordTrace tailWord_1967061 prefixEnd_1967061 673365179809222398994105 := by
  unfold tailWord_1967061
  simp only [CollatzResearch.WordTrace]
  refine ⟨71744608726681419117781037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47829739151120946078520691 71744608726681419117781037)
  ·
    refine ⟨26904228272505532169167889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71744608726681419117781037 26904228272505532169167889)
    ·
      refine ⟨20178171204379149126875917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26904228272505532169167889 20178171204379149126875917)
      ·
        refine ⟨7566814201642180922578469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20178171204379149126875917 7566814201642180922578469)
        ·
          refine ⟨1418777662807908922983463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7566814201642180922578469 1418777662807908922983463)
          ·
            refine ⟨2128166494211863384475195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418777662807908922983463 2128166494211863384475195)
            ·
              refine ⟨3192249741317795076712793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2128166494211863384475195 3192249741317795076712793)
              ·
                refine ⟨2394187305988346307534595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3192249741317795076712793 2394187305988346307534595)
                ·
                  refine ⟨3591280958982519461301893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2394187305988346307534595 3591280958982519461301893)
                  ·
                    refine ⟨673365179809222398994105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3591280958982519461301893 673365179809222398994105)
                    ·
                      rfl

theorem cell22_1967061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_1967061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967061 prefixEnd_1967061 := by exact prefixLift 1967061
  have htrace : WordTrace (prefixWord ++ tailWord_1967061) baseStart_1967061 baseEnd_1967061 := by
    simpa [prefixWord, tailWord_1967061, baseEnd_1967061] using wordTrace_append hprefix tailTrace_1967061
  have hstable : (prefixWord ++ tailWord_1967061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967061).length < 2 ^ (prefixWord ++ tailWord_1967061).sum := by decide
  have hdescent : baseEnd_1967061 < baseStart_1967061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967074 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1967074 : Nat := 118140960795 + 1967074 * 2 ^ 59
def prefixEnd_1967074 : Nat := 4983230072969 + 3 ^ 40 * 1967074 * 2
def baseEnd_1967074 : Nat := 673369629974894698419065

theorem tailTrace_1967074 : CollatzResearch.WordTrace tailWord_1967074 prefixEnd_1967074 673369629974894698419065 := by
  unfold tailWord_1967074
  simp only [CollatzResearch.WordTrace]
  refine ⟨17936270718908580584501069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47830055250422881558669517 17936270718908580584501069)
  ·
    refine ⟨6726101519590717719187901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17936270718908580584501069 6726101519590717719187901)
    ·
      refine ⟨2522288069846519144695463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6726101519590717719187901 2522288069846519144695463)
      ·
        refine ⟨3783432104769778717043195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522288069846519144695463 3783432104769778717043195)
        ·
          refine ⟨5675148157154668075564793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783432104769778717043195 5675148157154668075564793)
          ·
            refine ⟨4256361117866001056673595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5675148157154668075564793 4256361117866001056673595)
            ·
              refine ⟨6384541676799001585010393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4256361117866001056673595 6384541676799001585010393)
              ·
                refine ⟨4788406257599251188757795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6384541676799001585010393 4788406257599251188757795)
                ·
                  refine ⟨7182609386398876783136693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4788406257599251188757795 7182609386398876783136693)
                  ·
                    refine ⟨673369629974894698419065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7182609386398876783136693 673369629974894698419065)
                    ·
                      rfl

theorem cell22_1967074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1967074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967074 prefixEnd_1967074 := by exact prefixLift 1967074
  have htrace : WordTrace (prefixWord ++ tailWord_1967074) baseStart_1967074 baseEnd_1967074 := by
    simpa [prefixWord, tailWord_1967074, baseEnd_1967074] using wordTrace_append hprefix tailTrace_1967074
  have hstable : (prefixWord ++ tailWord_1967074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967074).length < 2 ^ (prefixWord ++ tailWord_1967074).sum := by decide
  have hdescent : baseEnd_1967074 < baseStart_1967074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967100 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_1967100 : Nat := 118140960795 + 1967100 * 2 ^ 59
def prefixEnd_1967100 : Nat := 4983230072969 + 3 ^ 40 * 1967100 * 2
def baseEnd_1967100 : Nat := 673378530306239297268985

theorem tailTrace_1967100 : CollatzResearch.WordTrace tailWord_1967100 prefixEnd_1967100 673378530306239297268985 := by
  unfold tailWord_1967100
  simp only [CollatzResearch.WordTrace]
  refine ⟨35873015586770064389225377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47830687449026752518967169 35873015586770064389225377)
  ·
    refine ⟨26904761690077548291919033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35873015586770064389225377 26904761690077548291919033)
    ·
      refine ⟨20178571267558161218939275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26904761690077548291919033 20178571267558161218939275)
      ·
        refine ⟨30267856901337241828408913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20178571267558161218939275 30267856901337241828408913)
        ·
          refine ⟨22700892676002931371306685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30267856901337241828408913 22700892676002931371306685)
          ·
            refine ⟨8512834753501099264240007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22700892676002931371306685 8512834753501099264240007)
            ·
              refine ⟨12769252130251648896360011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8512834753501099264240007 12769252130251648896360011)
              ·
                refine ⟨19153878195377473344540017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12769252130251648896360011 19153878195377473344540017)
                ·
                  refine ⟨14365408646533105008405013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19153878195377473344540017 14365408646533105008405013)
                  ·
                    refine ⟨673378530306239297268985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14365408646533105008405013 673378530306239297268985)
                    ·
                      rfl

theorem cell22_1967100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_1967100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967100 prefixEnd_1967100 := by exact prefixLift 1967100
  have htrace : WordTrace (prefixWord ++ tailWord_1967100) baseStart_1967100 baseEnd_1967100 := by
    simpa [prefixWord, tailWord_1967100, baseEnd_1967100] using wordTrace_append hprefix tailTrace_1967100
  have hstable : (prefixWord ++ tailWord_1967100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967100).length < 2 ^ (prefixWord ++ tailWord_1967100).sum := by decide
  have hdescent : baseEnd_1967100 < baseStart_1967100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967130 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_1967130 : Nat := 118140960795 + 1967130 * 2 ^ 59
def prefixEnd_1967130 : Nat := 4983230072969 + 3 ^ 40 * 1967130 * 2
def baseEnd_1967130 : Nat := 673388799919329219018893

theorem tailTrace_1967130 : CollatzResearch.WordTrace tailWord_1967130 prefixEnd_1967130 673388799919329219018893 := by
  unfold tailWord_1967130
  simp only [CollatzResearch.WordTrace]
  refine ⟨17936781340857860975510711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47831416908954295934695229 17936781340857860975510711)
  ·
    refine ⟨26905172011286791463266067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17936781340857860975510711 26905172011286791463266067)
    ·
      refine ⟨40357758016930187194899101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26905172011286791463266067 40357758016930187194899101)
      ·
        refine ⟨15134159256348820198087163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40357758016930187194899101 15134159256348820198087163)
        ·
          refine ⟨22701238884523230297130745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15134159256348820198087163 22701238884523230297130745)
          ·
            refine ⟨17025929163392422722848059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22701238884523230297130745 17025929163392422722848059)
            ·
              refine ⟨25538893745088634084272089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17025929163392422722848059 25538893745088634084272089)
              ·
                refine ⟨19154170308816475563204067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25538893745088634084272089 19154170308816475563204067)
                ·
                  refine ⟨28731255463224713344806101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19154170308816475563204067 28731255463224713344806101)
                  ·
                    refine ⟨673388799919329219018893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28731255463224713344806101 673388799919329219018893)
                    ·
                      rfl

theorem cell22_1967130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_1967130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967130 prefixEnd_1967130 := by exact prefixLift 1967130
  have htrace : WordTrace (prefixWord ++ tailWord_1967130) baseStart_1967130 baseEnd_1967130 := by
    simpa [prefixWord, tailWord_1967130, baseEnd_1967130] using wordTrace_append hprefix tailTrace_1967130
  have hstable : (prefixWord ++ tailWord_1967130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967130).length < 2 ^ (prefixWord ++ tailWord_1967130).sum := by decide
  have hdescent : baseEnd_1967130 < baseStart_1967130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967166 : List Nat := [4, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_1967166 : Nat := 118140960795 + 1967166 * 2 ^ 59
def prefixEnd_1967166 : Nat := 4983230072969 + 3 ^ 40 * 1967166 * 2
def baseEnd_1967166 : Nat := 224467041151679041706261

theorem tailTrace_1967166 : CollatzResearch.WordTrace tailWord_1967166 prefixEnd_1967166 224467041151679041706261 := by
  unfold tailWord_1967166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8968554798912627756294169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47832292260867348033568901 8968554798912627756294169)
  ·
    refine ⟨6726416099184470817220627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8968554798912627756294169 6726416099184470817220627)
    ·
      refine ⟨10089624148776706225830941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6726416099184470817220627 10089624148776706225830941)
      ·
        refine ⟨3783609055791264834686603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10089624148776706225830941 3783609055791264834686603)
        ·
          refine ⟨5675413583686897252029905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3783609055791264834686603 5675413583686897252029905)
          ·
            refine ⟨4256560187765172939022429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5675413583686897252029905 4256560187765172939022429)
            ·
              refine ⟨1596210070411939852133411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4256560187765172939022429 1596210070411939852133411)
              ·
                refine ⟨2394315105617909778200117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596210070411939852133411 2394315105617909778200117)
                ·
                  refine ⟨224467041151679041706261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2394315105617909778200117 224467041151679041706261)
                  ·
                    rfl

theorem cell22_1967166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_1967166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967166 prefixEnd_1967166 := by exact prefixLift 1967166
  have htrace : WordTrace (prefixWord ++ tailWord_1967166) baseStart_1967166 baseEnd_1967166 := by
    simpa [prefixWord, tailWord_1967166, baseEnd_1967166] using wordTrace_append hprefix tailTrace_1967166
  have hstable : (prefixWord ++ tailWord_1967166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967166).length < 2 ^ (prefixWord ++ tailWord_1967166).sum := by decide
  have hdescent : baseEnd_1967166 < baseStart_1967166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967192 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 6, 3]
def baseStart_1967192 : Nat := 118140960795 + 1967192 * 2 ^ 59
def prefixEnd_1967192 : Nat := 4983230072969 + 3 ^ 40 * 1967192 * 2
def baseEnd_1967192 : Nat := 673410023786381723968703

theorem tailTrace_1967192 : CollatzResearch.WordTrace tailWord_1967192 prefixEnd_1967192 673410023786381723968703 := by
  unfold tailWord_1967192
  simp only [CollatzResearch.WordTrace]
  refine ⟨35874693344603414245399915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47832924459471218993866553 35874693344603414245399915)
  ·
    refine ⟨53812040016905121368099873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35874693344603414245399915 53812040016905121368099873)
    ·
      refine ⟨40359030012678841026074905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53812040016905121368099873 40359030012678841026074905)
      ·
        refine ⟨30269272509509130769556179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40359030012678841026074905 30269272509509130769556179)
        ·
          refine ⟨45403908764263696154334269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30269272509509130769556179 45403908764263696154334269)
          ·
            refine ⟨17026465786598886057875351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45403908764263696154334269 17026465786598886057875351)
            ·
              refine ⟨25539698679898329086813027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17026465786598886057875351 25539698679898329086813027)
              ·
                refine ⟨38309548019847493630219541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25539698679898329086813027 38309548019847493630219541)
                ·
                  refine ⟨1795760063430351263916541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38309548019847493630219541 1795760063430351263916541)
                  ·
                    refine ⟨673410023786381723968703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1795760063430351263916541 673410023786381723968703)
                    ·
                      rfl

theorem cell22_1967192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_1967192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967192 prefixEnd_1967192 := by exact prefixLift 1967192
  have htrace : WordTrace (prefixWord ++ tailWord_1967192) baseStart_1967192 baseEnd_1967192 := by
    simpa [prefixWord, tailWord_1967192, baseEnd_1967192] using wordTrace_append hprefix tailTrace_1967192
  have hstable : (prefixWord ++ tailWord_1967192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967192).length < 2 ^ (prefixWord ++ tailWord_1967192).sum := by decide
  have hdescent : baseEnd_1967192 < baseStart_1967192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967207 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1967207 : Nat := 118140960795 + 1967207 * 2 ^ 59
def prefixEnd_1967207 : Nat := 4983230072969 + 3 ^ 40 * 1967207 * 2
def baseEnd_1967207 : Nat := 673415158592926684843657

theorem tailTrace_1967207 : CollatzResearch.WordTrace tailWord_1967207 prefixEnd_1967207 673415158592926684843657 := by
  unfold tailWord_1967207
  simp only [CollatzResearch.WordTrace]
  refine ⟨71749933784152486052595875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47833289189434990701730583 71749933784152486052595875)
  ·
    refine ⟨107624900676228729078893813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71749933784152486052595875 107624900676228729078893813)
    ·
      refine ⟨10089834438396443351146295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107624900676228729078893813 10089834438396443351146295)
      ·
        refine ⟨15134751657594665026719443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10089834438396443351146295 15134751657594665026719443)
        ·
          refine ⟨22702127486391997540079165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15134751657594665026719443 22702127486391997540079165)
          ·
            refine ⟨8513297807396999077529687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22702127486391997540079165 8513297807396999077529687)
            ·
              refine ⟨12769946711095498616294531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8513297807396999077529687 12769946711095498616294531)
              ·
                refine ⟨19154920066643247924441797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12769946711095498616294531 19154920066643247924441797)
                ·
                  refine ⟨3591547512495608985832837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19154920066643247924441797 3591547512495608985832837)
                  ·
                    refine ⟨673415158592926684843657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3591547512495608985832837 673415158592926684843657)
                    ·
                      rfl

theorem cell22_1967207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1967207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967207 prefixEnd_1967207 := by exact prefixLift 1967207
  have htrace : WordTrace (prefixWord ++ tailWord_1967207) baseStart_1967207 baseEnd_1967207 := by
    simpa [prefixWord, tailWord_1967207, baseEnd_1967207] using wordTrace_append hprefix tailTrace_1967207
  have hstable : (prefixWord ++ tailWord_1967207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967207).length < 2 ^ (prefixWord ++ tailWord_1967207).sum := by decide
  have hdescent : baseEnd_1967207 < baseStart_1967207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967282 : List Nat := [3, 2, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_1967282 : Nat := 118140960795 + 1967282 * 2 ^ 59
def prefixEnd_1967282 : Nat := 4983230072969 + 3 ^ 40 * 1967282 * 2
def baseEnd_1967282 : Nat := 673440832625651489218427

theorem tailTrace_1967282 : CollatzResearch.WordTrace tailWord_1967282 prefixEnd_1967282 673440832625651489218427 := by
  unfold tailWord_1967282
  simp only [CollatzResearch.WordTrace]
  refine ⟨17938167314720193465394025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47835112839253849241050733 17938167314720193465394025)
  ·
    refine ⟨13453625486040145099045519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17938167314720193465394025 13453625486040145099045519)
    ·
      refine ⟨20180438229060217648568279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13453625486040145099045519 20180438229060217648568279)
      ·
        refine ⟨30270657343590326472852419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20180438229060217648568279 30270657343590326472852419)
        ·
          refine ⟨45405986015385489709278629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30270657343590326472852419 45405986015385489709278629)
          ·
            refine ⟨8513622377884779320489743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45405986015385489709278629 8513622377884779320489743)
            ·
              refine ⟨12770433566827168980734615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8513622377884779320489743 12770433566827168980734615)
              ·
                refine ⟨19155650350240753471101923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12770433566827168980734615 19155650350240753471101923)
                ·
                  refine ⟨28733475525361130206652885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19155650350240753471101923 28733475525361130206652885)
                  ·
                    refine ⟨673440832625651489218427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28733475525361130206652885 673440832625651489218427)
                    ·
                      rfl

theorem cell22_1967282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_1967282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967282 prefixEnd_1967282 := by exact prefixLift 1967282
  have htrace : WordTrace (prefixWord ++ tailWord_1967282) baseStart_1967282 baseEnd_1967282 := by
    simpa [prefixWord, tailWord_1967282, baseEnd_1967282] using wordTrace_append hprefix tailTrace_1967282
  have hstable : (prefixWord ++ tailWord_1967282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967282).length < 2 ^ (prefixWord ++ tailWord_1967282).sum := by decide
  have hdescent : baseEnd_1967282 < baseStart_1967282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967327 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 3, 5]
def baseStart_1967327 : Nat := 118140960795 + 1967327 * 2 ^ 59
def prefixEnd_1967327 : Nat := 4983230072969 + 3 ^ 40 * 1967327 * 2
def baseEnd_1967327 : Nat := 673456237045286371843289

theorem tailTrace_1967327 : CollatzResearch.WordTrace tailWord_1967327 prefixEnd_1967327 673456237045286371843289 := by
  unfold tailWord_1967327
  simp only [CollatzResearch.WordTrace]
  refine ⟨71754310543717746546964235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47836207029145164364642823 71754310543717746546964235)
  ·
    refine ⟨107631465815576619820446353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71754310543717746546964235 107631465815576619820446353)
    ·
      refine ⟨80723599361682464865334765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107631465815576619820446353 80723599361682464865334765)
      ·
        refine ⟨30271349760630924324500537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80723599361682464865334765 30271349760630924324500537)
        ·
          refine ⟨22703512320473193243375403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30271349760630924324500537 22703512320473193243375403)
          ·
            refine ⟨34055268480709789865063105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22703512320473193243375403 34055268480709789865063105)
            ·
              refine ⟨25541451360532342398797329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34055268480709789865063105 25541451360532342398797329)
              ·
                refine ⟨19156088520399256799097997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25541451360532342398797329 19156088520399256799097997)
                ·
                  refine ⟨7183533195149721299661749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19156088520399256799097997 7183533195149721299661749)
                  ·
                    refine ⟨673456237045286371843289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7183533195149721299661749 673456237045286371843289)
                    ·
                      rfl

theorem cell22_1967327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_1967327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967327 prefixEnd_1967327 := by exact prefixLift 1967327
  have htrace : WordTrace (prefixWord ++ tailWord_1967327) baseStart_1967327 baseEnd_1967327 := by
    simpa [prefixWord, tailWord_1967327, baseEnd_1967327] using wordTrace_append hprefix tailTrace_1967327
  have hstable : (prefixWord ++ tailWord_1967327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967327).length < 2 ^ (prefixWord ++ tailWord_1967327).sum := by decide
  have hdescent : baseEnd_1967327 < baseStart_1967327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967329 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 6]
def baseStart_1967329 : Nat := 118140960795 + 1967329 * 2 ^ 59
def prefixEnd_1967329 : Nat := 4983230072969 + 3 ^ 40 * 1967329 * 2
def baseEnd_1967329 : Nat := 224485640562053011097761

theorem tailTrace_1967329 : CollatzResearch.WordTrace tailWord_1967329 prefixEnd_1967329 224485640562053011097761 := by
  unfold tailWord_1967329
  simp only [CollatzResearch.WordTrace]
  refine ⟨71754383489710500888537041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47836255659807000592358027 71754383489710500888537041)
  ·
    refine ⟨53815787617282875666402781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71754383489710500888537041 53815787617282875666402781)
    ·
      refine ⟨20180920356481078374901043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53815787617282875666402781 20180920356481078374901043)
      ·
        refine ⟨30271380534721617562351565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20180920356481078374901043 30271380534721617562351565)
        ·
          refine ⟨11351767700520606585881837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30271380534721617562351565 11351767700520606585881837)
          ·
            refine ⟨4256912887695227469705689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11351767700520606585881837 4256912887695227469705689)
            ·
              refine ⟨3192684665771420602279267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4256912887695227469705689 3192684665771420602279267)
              ·
                refine ⟨4789026998657130903418901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3192684665771420602279267 4789026998657130903418901)
                ·
                  refine ⟨224485640562053011097761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4789026998657130903418901 224485640562053011097761)
                  ·
                    rfl

theorem cell22_1967329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 6].length) (baseStart_1967329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967329 prefixEnd_1967329 := by exact prefixLift 1967329
  have htrace : WordTrace (prefixWord ++ tailWord_1967329) baseStart_1967329 baseEnd_1967329 := by
    simpa [prefixWord, tailWord_1967329, baseEnd_1967329] using wordTrace_append hprefix tailTrace_1967329
  have hstable : (prefixWord ++ tailWord_1967329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967329).length < 2 ^ (prefixWord ++ tailWord_1967329).sum := by decide
  have hdescent : baseEnd_1967329 < baseStart_1967329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967374 : List Nat := [4, 1, 1, 2, 1, 5, 8]
def baseStart_1967374 : Nat := 118140960795 + 1967374 * 2 ^ 59
def prefixEnd_1967374 : Nat := 4983230072969 + 3 ^ 40 * 1967374 * 2
def baseEnd_1967374 : Nat := 24943419485399774663635

theorem tailTrace_1967374 : CollatzResearch.WordTrace tailWord_1967374 prefixEnd_1967374 24943419485399774663635 := by
  unfold tailWord_1967374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8969503096818434196740647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47837349849698315715950117 8969503096818434196740647)
  ·
    refine ⟨13454254645227651295110971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8969503096818434196740647 13454254645227651295110971)
    ·
      refine ⟨20181381967841476942666457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13454254645227651295110971 20181381967841476942666457)
      ·
        refine ⟨15136036475881107706999843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20181381967841476942666457 15136036475881107706999843)
        ·
          refine ⟨22704054713821661560499765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15136036475881107706999843 22704054713821661560499765)
          ·
            refine ⟨2128505129420780771296853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22704054713821661560499765 2128505129420780771296853)
            ·
              refine ⟨24943419485399774663635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2128505129420780771296853 24943419485399774663635)
              ·
                rfl

theorem cell22_1967374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 8].length) (baseStart_1967374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967374 prefixEnd_1967374 := by exact prefixLift 1967374
  have htrace : WordTrace (prefixWord ++ tailWord_1967374) baseStart_1967374 baseEnd_1967374 := by
    simpa [prefixWord, tailWord_1967374, baseEnd_1967374] using wordTrace_append hprefix tailTrace_1967374
  have hstable : (prefixWord ++ tailWord_1967374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967374).length < 2 ^ (prefixWord ++ tailWord_1967374).sum := by decide
  have hdescent : baseEnd_1967374 < baseStart_1967374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967387 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 2, 6]
def baseStart_1967387 : Nat := 118140960795 + 1967387 * 2 ^ 59
def prefixEnd_1967387 : Nat := 4983230072969 + 3 ^ 40 * 1967387 * 2
def baseEnd_1967387 : Nat := 673476776271466215343105

theorem tailTrace_1967387 : CollatzResearch.WordTrace tailWord_1967387 prefixEnd_1967387 673476776271466215343105 := by
  unfold tailWord_1967387
  simp only [CollatzResearch.WordTrace]
  refine ⟨71756498923500376794148415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47837665949000251196098943 71756498923500376794148415)
  ·
    refine ⟨107634748385250565191222623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71756498923500376794148415 107634748385250565191222623)
    ·
      refine ⟨161452122577875847786833935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107634748385250565191222623 161452122577875847786833935)
      ·
        refine ⟨242178183866813771680250903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161452122577875847786833935 242178183866813771680250903)
        ·
          refine ⟨363267275800220657520376355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242178183866813771680250903 363267275800220657520376355)
          ·
            refine ⟨544900913700330986280564533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363267275800220657520376355 544900913700330986280564533)
            ·
              refine ⟨51084460659406029963802925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 544900913700330986280564533 51084460659406029963802925)
              ·
                refine ⟨19156672747277261236426097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51084460659406029963802925 19156672747277261236426097)
                ·
                  refine ⟨14367504560457945927319573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19156672747277261236426097 14367504560457945927319573)
                  ·
                    refine ⟨673476776271466215343105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14367504560457945927319573 673476776271466215343105)
                    ·
                      rfl

theorem cell22_1967387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_1967387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967387 prefixEnd_1967387 := by exact prefixLift 1967387
  have htrace : WordTrace (prefixWord ++ tailWord_1967387) baseStart_1967387 baseEnd_1967387 := by
    simpa [prefixWord, tailWord_1967387, baseEnd_1967387] using wordTrace_append hprefix tailTrace_1967387
  have hstable : (prefixWord ++ tailWord_1967387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967387).length < 2 ^ (prefixWord ++ tailWord_1967387).sum := by decide
  have hdescent : baseEnd_1967387 < baseStart_1967387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967436 : List Nat := [2, 2, 1, 3, 2, 3, 2, 2, 5]
def baseStart_1967436 : Nat := 118140960795 + 1967436 * 2 ^ 59
def prefixEnd_1967436 : Nat := 4983230072969 + 3 ^ 40 * 1967436 * 2
def baseEnd_1967436 : Nat := 224497849990948806955985

theorem tailTrace_1967436 : CollatzResearch.WordTrace tailWord_1967436 prefixEnd_1967436 224497849990948806955985 := by
  unfold tailWord_1967436
  simp only [CollatzResearch.WordTrace]
  refine ⟨35879143050161429081341081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47838857400215238775121441 35879143050161429081341081)
  ·
    refine ⟨26909357287621071811005811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35879143050161429081341081 26909357287621071811005811)
    ·
      refine ⟨40364035931431607716508717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26909357287621071811005811 40364035931431607716508717)
      ·
        refine ⟨15136513474286852893690769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40364035931431607716508717 15136513474286852893690769)
        ·
          refine ⟨11352385105715139670268077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15136513474286852893690769 11352385105715139670268077)
          ·
            refine ⟨4257144414643177376350529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11352385105715139670268077 4257144414643177376350529)
            ·
              refine ⟨3192858310982383032262897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4257144414643177376350529 3192858310982383032262897)
              ·
                refine ⟨2394643733236787274197173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3192858310982383032262897 2394643733236787274197173)
                ·
                  refine ⟨224497849990948806955985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2394643733236787274197173 224497849990948806955985)
                  ·
                    rfl

theorem cell22_1967436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_1967436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967436 prefixEnd_1967436 := by exact prefixLift 1967436
  have htrace : WordTrace (prefixWord ++ tailWord_1967436) baseStart_1967436 baseEnd_1967436 := by
    simpa [prefixWord, tailWord_1967436, baseEnd_1967436] using wordTrace_append hprefix tailTrace_1967436
  have hstable : (prefixWord ++ tailWord_1967436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967436).length < 2 ^ (prefixWord ++ tailWord_1967436).sum := by decide
  have hdescent : baseEnd_1967436 < baseStart_1967436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967449 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 3, 4]
def baseStart_1967449 : Nat := 118140960795 + 1967449 * 2 ^ 59
def prefixEnd_1967449 : Nat := 4983230072969 + 3 ^ 40 * 1967449 * 2
def baseEnd_1967449 : Nat := 673498000138518720292915

theorem tailTrace_1967449 : CollatzResearch.WordTrace tailWord_1967449 prefixEnd_1967449 673498000138518720292915 := by
  unfold tailWord_1967449
  simp only [CollatzResearch.WordTrace]
  refine ⟨71758760249275761382905401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47839173499517174255270267 71758760249275761382905401)
  ·
    refine ⟨53819070186956821037179051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71758760249275761382905401 53819070186956821037179051)
    ·
      refine ⟨80728605280435231555768577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53819070186956821037179051 80728605280435231555768577)
      ·
        refine ⟨60546453960326423666826433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80728605280435231555768577 60546453960326423666826433)
        ·
          refine ⟨45409840470244817750119825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60546453960326423666826433 45409840470244817750119825)
          ·
            refine ⟨34057380352683613312589869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45409840470244817750119825 34057380352683613312589869)
            ·
              refine ⟨12771517632256354992221201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34057380352683613312589869 12771517632256354992221201)
              ·
                refine ⟨9578638224192266244165901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12771517632256354992221201 9578638224192266244165901)
                ·
                  refine ⟨3591989334072099841562213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9578638224192266244165901 3591989334072099841562213)
                  ·
                    refine ⟨673498000138518720292915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3591989334072099841562213 673498000138518720292915)
                    ·
                      rfl

theorem cell22_1967449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_1967449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967449 prefixEnd_1967449 := by exact prefixLift 1967449
  have htrace : WordTrace (prefixWord ++ tailWord_1967449) baseStart_1967449 baseEnd_1967449 := by
    simpa [prefixWord, tailWord_1967449, baseEnd_1967449] using wordTrace_append hprefix tailTrace_1967449
  have hstable : (prefixWord ++ tailWord_1967449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967449).length < 2 ^ (prefixWord ++ tailWord_1967449).sum := by decide
  have hdescent : baseEnd_1967449 < baseStart_1967449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967479 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 1, 5]
def baseStart_1967479 : Nat := 118140960795 + 1967479 * 2 ^ 59
def prefixEnd_1967479 : Nat := 4983230072969 + 3 ^ 40 * 1967479 * 2
def baseEnd_1967479 : Nat := 673508269751608642042823

theorem tailTrace_1967479 : CollatzResearch.WordTrace tailWord_1967479 prefixEnd_1967479 673508269751608642042823 := by
  unfold tailWord_1967479
  simp only [CollatzResearch.WordTrace]
  refine ⟨71759854439167076506497491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47839902959444717670998327 71759854439167076506497491)
  ·
    refine ⟨107639781658750614759746237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71759854439167076506497491 107639781658750614759746237)
    ·
      refine ⟨40364918122031480534904839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107639781658750614759746237 40364918122031480534904839)
      ·
        refine ⟨60547377183047220802357259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40364918122031480534904839 60547377183047220802357259)
        ·
          refine ⟨90821065774570831203535889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60547377183047220802357259 90821065774570831203535889)
          ·
            refine ⟨68115799330928123402651917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90821065774570831203535889 68115799330928123402651917)
            ·
              refine ⟨25543424749098046275994469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68115799330928123402651917 25543424749098046275994469)
              ·
                refine ⟨4789392140455883676748963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25543424749098046275994469 4789392140455883676748963)
                ·
                  refine ⟨7184088210683825515123445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789392140455883676748963 7184088210683825515123445)
                  ·
                    refine ⟨673508269751608642042823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7184088210683825515123445 673508269751608642042823)
                    ·
                      rfl

theorem cell22_1967479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_1967479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967479 prefixEnd_1967479 := by exact prefixLift 1967479
  have htrace : WordTrace (prefixWord ++ tailWord_1967479) baseStart_1967479 baseEnd_1967479 := by
    simpa [prefixWord, tailWord_1967479, baseEnd_1967479] using wordTrace_append hprefix tailTrace_1967479
  have hstable : (prefixWord ++ tailWord_1967479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967479).length < 2 ^ (prefixWord ++ tailWord_1967479).sum := by decide
  have hdescent : baseEnd_1967479 < baseStart_1967479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967481 : List Nat := [1, 2, 1, 3, 2, 1, 3, 5, 4]
def baseStart_1967481 : Nat := 118140960795 + 1967481 * 2 ^ 59
def prefixEnd_1967481 : Nat := 4983230072969 + 3 ^ 40 * 1967481 * 2
def baseEnd_1967481 : Nat := 224502984797493767830939

theorem tailTrace_1967481 : CollatzResearch.WordTrace tailWord_1967481 prefixEnd_1967481 224502984797493767830939 := by
  unfold tailWord_1967481
  simp only [CollatzResearch.WordTrace]
  refine ⟨71759927385159830848070297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47839951590106553898713531 71759927385159830848070297)
  ·
    refine ⟨53819945538869873136052723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71759927385159830848070297 53819945538869873136052723)
    ·
      refine ⟨80729918308304809704079085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53819945538869873136052723 80729918308304809704079085)
      ·
        refine ⟨30273719365614303639029657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80729918308304809704079085 30273719365614303639029657)
        ·
          refine ⟨22705289524210727729272243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30273719365614303639029657 22705289524210727729272243)
          ·
            refine ⟨34057934286316091593908365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22705289524210727729272243 34057934286316091593908365)
            ·
              refine ⟨12771725357368534347715637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34057934286316091593908365 12771725357368534347715637)
              ·
                refine ⟨1197349252253300095098341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12771725357368534347715637 1197349252253300095098341)
                ·
                  refine ⟨224502984797493767830939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1197349252253300095098341 224502984797493767830939)
                  ·
                    rfl

theorem cell22_1967481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 4].length) (baseStart_1967481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967481 prefixEnd_1967481 := by exact prefixLift 1967481
  have htrace : WordTrace (prefixWord ++ tailWord_1967481) baseStart_1967481 baseEnd_1967481 := by
    simpa [prefixWord, tailWord_1967481, baseEnd_1967481] using wordTrace_append hprefix tailTrace_1967481
  have hstable : (prefixWord ++ tailWord_1967481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967481).length < 2 ^ (prefixWord ++ tailWord_1967481).sum := by decide
  have hdescent : baseEnd_1967481 < baseStart_1967481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967524 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_1967524 : Nat := 118140960795 + 1967524 * 2 ^ 59
def prefixEnd_1967524 : Nat := 4983230072969 + 3 ^ 40 * 1967524 * 2
def baseEnd_1967524 : Nat := 673523674171243524667685

theorem tailTrace_1967524 : CollatzResearch.WordTrace tailWord_1967524 prefixEnd_1967524 673523674171243524667685 := by
  unfold tailWord_1967524
  simp only [CollatzResearch.WordTrace]
  refine ⟨35880747862002024595942813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47840997149336032794590417 35880747862002024595942813)
  ·
    refine ⟨13455280448250759223478555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35880747862002024595942813 13455280448250759223478555)
    ·
      refine ⟨20182920672376138835217833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13455280448250759223478555 20182920672376138835217833)
      ·
        refine ⟨15137190504282104126413375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20182920672376138835217833 15137190504282104126413375)
        ·
          refine ⟨22705785756423156189620063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15137190504282104126413375 22705785756423156189620063)
          ·
            refine ⟨34058678634634734284430095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22705785756423156189620063 34058678634634734284430095)
            ·
              refine ⟨51088017951952101426645143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34058678634634734284430095 51088017951952101426645143)
              ·
                refine ⟨76632026927928152139967715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51088017951952101426645143 76632026927928152139967715)
                ·
                  refine ⟨114948040391892228209951573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76632026927928152139967715 114948040391892228209951573)
                  ·
                    refine ⟨673523674171243524667685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 114948040391892228209951573 673523674171243524667685)
                    ·
                      rfl

theorem cell22_1967524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_1967524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967524 prefixEnd_1967524 := by exact prefixLift 1967524
  have htrace : WordTrace (prefixWord ++ tailWord_1967524) baseStart_1967524 baseEnd_1967524 := by
    simpa [prefixWord, tailWord_1967524, baseEnd_1967524] using wordTrace_append hprefix tailTrace_1967524
  have hstable : (prefixWord ++ tailWord_1967524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967524).length < 2 ^ (prefixWord ++ tailWord_1967524).sum := by decide
  have hdescent : baseEnd_1967524 < baseStart_1967524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967605 : List Nat := [1, 3, 5, 1, 1, 2, 2, 2, 5]
def baseStart_1967605 : Nat := 118140960795 + 1967605 * 2 ^ 59
def prefixEnd_1967605 : Nat := 4983230072969 + 3 ^ 40 * 1967605 * 2
def baseEnd_1967605 : Nat := 224517134042195437797479

theorem tailTrace_1967605 : CollatzResearch.WordTrace tailWord_1967605 prefixEnd_1967605 224517134042195437797479 := by
  unfold tailWord_1967605
  simp only [CollatzResearch.WordTrace]
  refine ⟨71764450036710600025584269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47842966691140400017056179 71764450036710600025584269)
  ·
    refine ⟨26911668763766475009594101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71764450036710600025584269 26911668763766475009594101)
    ·
      refine ⟨2522968946603107032149447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26911668763766475009594101 2522968946603107032149447)
      ·
        refine ⟨3784453419904660548224171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2522968946603107032149447 3784453419904660548224171)
        ·
          refine ⟨5676680129856990822336257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784453419904660548224171 5676680129856990822336257)
          ·
            refine ⟨4257510097392743116752193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5676680129856990822336257 4257510097392743116752193)
            ·
              refine ⟨3193132573044557337564145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4257510097392743116752193 3193132573044557337564145)
              ·
                refine ⟨2394849429783418003173109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3193132573044557337564145 2394849429783418003173109)
                ·
                  refine ⟨224517134042195437797479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2394849429783418003173109 224517134042195437797479)
                  ·
                    rfl

theorem cell22_1967605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_1967605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967605 prefixEnd_1967605 := by exact prefixLift 1967605
  have htrace : WordTrace (prefixWord ++ tailWord_1967605) baseStart_1967605 baseEnd_1967605 := by
    simpa [prefixWord, tailWord_1967605, baseEnd_1967605] using wordTrace_append hprefix tailTrace_1967605
  have hstable : (prefixWord ++ tailWord_1967605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967605).length < 2 ^ (prefixWord ++ tailWord_1967605).sum := by decide
  have hdescent : baseEnd_1967605 < baseStart_1967605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967648 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 1, 5]
def baseStart_1967648 : Nat := 118140960795 + 1967648 * 2 ^ 59
def prefixEnd_1967648 : Nat := 4983230072969 + 3 ^ 40 * 1967648 * 2
def baseEnd_1967648 : Nat := 673566121905348534567305

theorem tailTrace_1967648 : CollatzResearch.WordTrace tailWord_1967648 prefixEnd_1967648 673566121905348534567305 := by
  unfold tailWord_1967648
  simp only [CollatzResearch.WordTrace]
  refine ⟨35883009187777409184699799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47844012250369878912933065 35883009187777409184699799)
  ·
    refine ⟨53824513781666113777049699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35883009187777409184699799 53824513781666113777049699)
    ·
      refine ⟨80736770672499170665574549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53824513781666113777049699 80736770672499170665574549)
      ·
        refine ⟨3784536125273398624948807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80736770672499170665574549 3784536125273398624948807)
        ·
          refine ⟨5676804187910097937423211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784536125273398624948807 5676804187910097937423211)
          ·
            refine ⟨8515206281865146906134817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5676804187910097937423211 8515206281865146906134817)
            ·
              refine ⟨6386404711398860179601113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8515206281865146906134817 6386404711398860179601113)
              ·
                refine ⟨4789803533549145134700835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6386404711398860179601113 4789803533549145134700835)
                ·
                  refine ⟨7184705300323717702051253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4789803533549145134700835 7184705300323717702051253)
                  ·
                    refine ⟨673566121905348534567305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7184705300323717702051253 673566121905348534567305)
                    ·
                      rfl

theorem cell22_1967648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_1967648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967648 prefixEnd_1967648 := by exact prefixLift 1967648
  have htrace : WordTrace (prefixWord ++ tailWord_1967648) baseStart_1967648 baseEnd_1967648 := by
    simpa [prefixWord, tailWord_1967648, baseEnd_1967648] using wordTrace_append hprefix tailTrace_1967648
  have hstable : (prefixWord ++ tailWord_1967648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967648).length < 2 ^ (prefixWord ++ tailWord_1967648).sum := by decide
  have hdescent : baseEnd_1967648 < baseStart_1967648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967721 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 4, 5]
def baseStart_1967721 : Nat := 118140960795 + 1967721 * 2 ^ 59
def prefixEnd_1967721 : Nat := 4983230072969 + 3 ^ 40 * 1967721 * 2
def baseEnd_1967721 : Nat := 673591111297200677492081

theorem tailTrace_1967721 : CollatzResearch.WordTrace tailWord_1967721 prefixEnd_1967721 673591111297200677492081 := by
  unfold tailWord_1967721
  simp only [CollatzResearch.WordTrace]
  refine ⟨71768680904290351836807017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47845787269526901224538011 71768680904290351836807017)
  ·
    refine ⟨53826510678217763877605263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71768680904290351836807017 53826510678217763877605263)
    ·
      refine ⟨80739766017326645816407895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53826510678217763877605263 80739766017326645816407895)
      ·
        refine ⟨121109649025989968724611843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80739766017326645816407895 121109649025989968724611843)
        ·
          refine ⟨181664473538984953086917765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121109649025989968724611843 181664473538984953086917765)
          ·
            refine ⟨34062088788559678703797081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 181664473538984953086917765 34062088788559678703797081)
            ·
              refine ⟨25546566591419759027847811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34062088788559678703797081 25546566591419759027847811)
              ·
                refine ⟨38319849887129638541771717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25546566591419759027847811 38319849887129638541771717)
                ·
                  refine ⟨7184971853836807226582197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38319849887129638541771717 7184971853836807226582197)
                  ·
                    refine ⟨673591111297200677492081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7184971853836807226582197 673591111297200677492081)
                    ·
                      rfl

theorem cell22_1967721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_1967721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967721 prefixEnd_1967721 := by exact prefixLift 1967721
  have htrace : WordTrace (prefixWord ++ tailWord_1967721) baseStart_1967721 baseEnd_1967721 := by
    simpa [prefixWord, tailWord_1967721, baseEnd_1967721] using wordTrace_append hprefix tailTrace_1967721
  have hstable : (prefixWord ++ tailWord_1967721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967721).length < 2 ^ (prefixWord ++ tailWord_1967721).sum := by decide
  have hdescent : baseEnd_1967721 < baseStart_1967721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967778 : List Nat := [3, 3, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_1967778 : Nat := 118140960795 + 1967778 * 2 ^ 59
def prefixEnd_1967778 : Nat := 4983230072969 + 3 ^ 40 * 1967778 * 2
def baseEnd_1967778 : Nat := 673610623562071528816907

theorem tailTrace_1967778 : CollatzResearch.WordTrace tailWord_1967778 prefixEnd_1967778 673610623562071528816907 := by
  unfold tailWord_1967778
  simp only [CollatzResearch.WordTrace]
  refine ⟨17942689966270962642907997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47847173243389233714421325 17942689966270962642907997)
  ·
    refine ⟨6728508737351610991090499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17942689966270962642907997 6728508737351610991090499)
    ·
      refine ⟨10092763106027416486635749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6728508737351610991090499 10092763106027416486635749)
      ·
        refine ⟨1892393082380140591244203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10092763106027416486635749 1892393082380140591244203)
        ·
          refine ⟨2838589623570210886866305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892393082380140591244203 2838589623570210886866305)
          ·
            refine ⟨2128942217677658165149729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2838589623570210886866305 2128942217677658165149729)
            ·
              refine ⟨1596706663258243623862297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2128942217677658165149729 1596706663258243623862297)
              ·
                refine ⟨1197529997443682717896723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1596706663258243623862297 1197529997443682717896723)
                ·
                  refine ⟨1796294996165524076845085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1197529997443682717896723 1796294996165524076845085)
                  ·
                    refine ⟨673610623562071528816907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1796294996165524076845085 673610623562071528816907)
                    ·
                      rfl

theorem cell22_1967778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_1967778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967778 prefixEnd_1967778 := by exact prefixLift 1967778
  have htrace : WordTrace (prefixWord ++ tailWord_1967778) baseStart_1967778 baseEnd_1967778 := by
    simpa [prefixWord, tailWord_1967778, baseEnd_1967778] using wordTrace_append hprefix tailTrace_1967778
  have hstable : (prefixWord ++ tailWord_1967778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967778).length < 2 ^ (prefixWord ++ tailWord_1967778).sum := by decide
  have hdescent : baseEnd_1967778 < baseStart_1967778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967821 : List Nat := [1, 6, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1967821 : Nat := 118140960795 + 1967821 * 2 ^ 59
def prefixEnd_1967821 : Nat := 4983230072969 + 3 ^ 40 * 1967821 * 2
def baseEnd_1967821 : Nat := 673625343340833749991775

theorem tailTrace_1967821 : CollatzResearch.WordTrace tailWord_1967821 prefixEnd_1967821 673625343340833749991775 := by
  unfold tailWord_1967821
  simp only [CollatzResearch.WordTrace]
  refine ⟨71772328203928068915447317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47848218802618712610298211 71772328203928068915447317)
  ·
    refine ⟨3364327884559128230411593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71772328203928068915447317 3364327884559128230411593)
    ·
      refine ⟨2523245913419346172808695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3364327884559128230411593 2523245913419346172808695)
      ·
        refine ⟨3784868870129019259213043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2523245913419346172808695 3784868870129019259213043)
        ·
          refine ⟨5677303305193528888819565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3784868870129019259213043 5677303305193528888819565)
          ·
            refine ⟨2128988739447573333307337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5677303305193528888819565 2128988739447573333307337)
            ·
              refine ⟨1596741554585679999980503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2128988739447573333307337 1596741554585679999980503)
              ·
                refine ⟨2395112331878519999970755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1596741554585679999980503 2395112331878519999970755)
                ·
                  refine ⟨3592668497817779999956133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395112331878519999970755 3592668497817779999956133)
                  ·
                    refine ⟨673625343340833749991775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3592668497817779999956133 673625343340833749991775)
                    ·
                      rfl

theorem cell22_1967821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1967821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967821 prefixEnd_1967821 := by exact prefixLift 1967821
  have htrace : WordTrace (prefixWord ++ tailWord_1967821) baseStart_1967821 baseEnd_1967821 := by
    simpa [prefixWord, tailWord_1967821, baseEnd_1967821] using wordTrace_append hprefix tailTrace_1967821
  have hstable : (prefixWord ++ tailWord_1967821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967821).length < 2 ^ (prefixWord ++ tailWord_1967821).sum := by decide
  have hdescent : baseEnd_1967821 < baseStart_1967821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967862 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_1967862 : Nat := 118140960795 + 1967862 * 2 ^ 59
def prefixEnd_1967862 : Nat := 4983230072969 + 3 ^ 40 * 1967862 * 2
def baseEnd_1967862 : Nat := 673639378478723309716649

theorem tailTrace_1967862 : CollatzResearch.WordTrace tailWord_1967862 prefixEnd_1967862 673639378478723309716649 := by
  unfold tailWord_1967862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4485863974798720807355615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47849215731186355278459893 4485863974798720807355615)
  ·
    refine ⟨6728795962198081211033423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4485863974798720807355615 6728795962198081211033423)
    ·
      refine ⟨10093193943297121816550135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6728795962198081211033423 10093193943297121816550135)
      ·
        refine ⟨15139790914945682724825203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10093193943297121816550135 15139790914945682724825203)
        ·
          refine ⟨22709686372418524087237805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15139790914945682724825203 22709686372418524087237805)
          ·
            refine ⟨8516132389656946532714177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22709686372418524087237805 8516132389656946532714177)
            ·
              refine ⟨6387099292242709899535633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8516132389656946532714177 6387099292242709899535633)
              ·
                refine ⟨4790324469182032424651725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6387099292242709899535633 4790324469182032424651725)
                ·
                  refine ⟨1796371675943262159244397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4790324469182032424651725 1796371675943262159244397)
                  ·
                    refine ⟨673639378478723309716649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1796371675943262159244397 673639378478723309716649)
                    ·
                      rfl

theorem cell22_1967862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_1967862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967862 prefixEnd_1967862 := by exact prefixLift 1967862
  have htrace : WordTrace (prefixWord ++ tailWord_1967862) baseStart_1967862 baseEnd_1967862 := by
    simpa [prefixWord, tailWord_1967862, baseEnd_1967862] using wordTrace_append hprefix tailTrace_1967862
  have hstable : (prefixWord ++ tailWord_1967862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967862).length < 2 ^ (prefixWord ++ tailWord_1967862).sum := by decide
  have hdescent : baseEnd_1967862 < baseStart_1967862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967873 : List Nat := [1, 2, 4, 1, 1, 1, 2, 2, 1, 7]
def baseStart_1967873 : Nat := 118140960795 + 1967873 * 2 ^ 59
def prefixEnd_1967873 : Nat := 4983230072969 + 3 ^ 40 * 1967873 * 2
def baseEnd_1967873 : Nat := 673643144003522947691615

theorem tailTrace_1967873 : CollatzResearch.WordTrace tailWord_1967873 prefixEnd_1967873 673643144003522947691615 := by
  unfold tailWord_1967873
  simp only [CollatzResearch.WordTrace]
  refine ⟨71774224799739681796340273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47849483199826454530893515 71774224799739681796340273)
  ·
    refine ⟨53830668599804761347255205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71774224799739681796340273 53830668599804761347255205)
    ·
      refine ⟨10093250362463392752610351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53830668599804761347255205 10093250362463392752610351)
      ·
        refine ⟨15139875543695089128915527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10093250362463392752610351 15139875543695089128915527)
        ·
          refine ⟨22709813315542633693373291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15139875543695089128915527 22709813315542633693373291)
          ·
            refine ⟨34064719973313950540059937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22709813315542633693373291 34064719973313950540059937)
            ·
              refine ⟨25548539979985462905044953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34064719973313950540059937 25548539979985462905044953)
              ·
                refine ⟨19161404984989097178783715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25548539979985462905044953 19161404984989097178783715)
                ·
                  refine ⟨28742107477483645768175573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19161404984989097178783715 28742107477483645768175573)
                  ·
                    refine ⟨673643144003522947691615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28742107477483645768175573 673643144003522947691615)
                    ·
                      rfl

theorem cell22_1967873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_1967873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967873 prefixEnd_1967873 := by exact prefixLift 1967873
  have htrace : WordTrace (prefixWord ++ tailWord_1967873) baseStart_1967873 baseEnd_1967873 := by
    simpa [prefixWord, tailWord_1967873, baseEnd_1967873] using wordTrace_append hprefix tailTrace_1967873
  have hstable : (prefixWord ++ tailWord_1967873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967873).length < 2 ^ (prefixWord ++ tailWord_1967873).sum := by decide
  have hdescent : baseEnd_1967873 < baseStart_1967873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967922 : List Nat := [3, 2, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_1967922 : Nat := 118140960795 + 1967922 * 2 ^ 59
def prefixEnd_1967922 : Nat := 4983230072969 + 3 ^ 40 * 1967922 * 2
def baseEnd_1967922 : Nat := 673659917704903153216465

theorem tailTrace_1967922 : CollatzResearch.WordTrace tailWord_1967922 prefixEnd_1967922 673659917704903153216465 := by
  unfold tailWord_1967922
  simp only [CollatzResearch.WordTrace]
  refine ⟨17944002994140540791218505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47850674651041442109916013 17944002994140540791218505)
  ·
    refine ⟨13458002245605405593413879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17944002994140540791218505 13458002245605405593413879)
    ·
      refine ⟨20187003368408108390120819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13458002245605405593413879 20187003368408108390120819)
      ·
        refine ⟨30280505052612162585181229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20187003368408108390120819 30280505052612162585181229)
        ·
          refine ⟨11355189394729560969442961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30280505052612162585181229 11355189394729560969442961)
          ·
            refine ⟨8516392046047170727082221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11355189394729560969442961 8516392046047170727082221)
            ·
              refine ⟨3193647017267689022655833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8516392046047170727082221 3193647017267689022655833)
              ·
                refine ⟨2395235262950766766991875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3193647017267689022655833 2395235262950766766991875)
                ·
                  refine ⟨3592852894426150150487813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395235262950766766991875 3592852894426150150487813)
                  ·
                    refine ⟨673659917704903153216465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3592852894426150150487813 673659917704903153216465)
                    ·
                      rfl

theorem cell22_1967922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_1967922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967922 prefixEnd_1967922 := by exact prefixLift 1967922
  have htrace : WordTrace (prefixWord ++ tailWord_1967922) baseStart_1967922 baseEnd_1967922 := by
    simpa [prefixWord, tailWord_1967922, baseEnd_1967922] using wordTrace_append hprefix tailTrace_1967922
  have hstable : (prefixWord ++ tailWord_1967922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967922).length < 2 ^ (prefixWord ++ tailWord_1967922).sum := by decide
  have hdescent : baseEnd_1967922 < baseStart_1967922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967948 : List Nat := [2, 2, 1, 3, 14]
def baseStart_1967948 : Nat := 118140960795 + 1967948 * 2 ^ 59
def prefixEnd_1967948 : Nat := 4983230072969 + 3 ^ 40 * 1967948 * 2
def baseEnd_1967948 : Nat := 2772299662700608033195

theorem tailTrace_1967948 : CollatzResearch.WordTrace tailWord_1967948 prefixEnd_1967948 2772299662700608033195 := by
  unfold tailWord_1967948
  simp only [CollatzResearch.WordTrace]
  refine ⟨35888480137233984802660249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47851306849645313070213665 35888480137233984802660249)
  ·
    refine ⟨26916360102925488601995187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35888480137233984802660249 26916360102925488601995187)
    ·
      refine ⟨40374540154388232902992781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26916360102925488601995187 40374540154388232902992781)
      ·
        refine ⟨15140452557895587338622293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40374540154388232902992781 15140452557895587338622293)
        ·
          refine ⟨2772299662700608033195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 15140452557895587338622293 2772299662700608033195)
          ·
            rfl

theorem cell22_1967948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 14].length) (baseStart_1967948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967948 prefixEnd_1967948 := by exact prefixLift 1967948
  have htrace : WordTrace (prefixWord ++ tailWord_1967948) baseStart_1967948 baseEnd_1967948 := by
    simpa [prefixWord, tailWord_1967948, baseEnd_1967948] using wordTrace_append hprefix tailTrace_1967948
  have hstable : (prefixWord ++ tailWord_1967948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967948).length < 2 ^ (prefixWord ++ tailWord_1967948).sum := by decide
  have hdescent : baseEnd_1967948 < baseStart_1967948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1967954 : List Nat := [3, 2, 2, 1, 1, 3, 4, 2, 4]
def baseStart_1967954 : Nat := 118140960795 + 1967954 * 2 ^ 59
def prefixEnd_1967954 : Nat := 4983230072969 + 3 ^ 40 * 1967954 * 2
def baseEnd_1967954 : Nat := 224556957319621912138789

theorem tailTrace_1967954 : CollatzResearch.WordTrace tailWord_1967954 prefixEnd_1967954 224556957319621912138789 := by
  unfold tailWord_1967954
  simp only [CollatzResearch.WordTrace]
  refine ⟨17944294778111558157509729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47851452741630821753359277 17944294778111558157509729)
  ·
    refine ⟨13458221083583668618132297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17944294778111558157509729 13458221083583668618132297)
    ·
      refine ⟨10093665812687751463599223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13458221083583668618132297 10093665812687751463599223)
      ·
        refine ⟨15140498719031627195398835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10093665812687751463599223 15140498719031627195398835)
        ·
          refine ⟨22710748078547440793098253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15140498719031627195398835 22710748078547440793098253)
          ·
            refine ⟨8516530529455290297411845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22710748078547440793098253 8516530529455290297411845)
            ·
              refine ⟨1596849474272866930764721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8516530529455290297411845 1596849474272866930764721)
              ·
                refine ⟨1197637105704650198073541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1596849474272866930764721 1197637105704650198073541)
                ·
                  refine ⟨224556957319621912138789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1197637105704650198073541 224556957319621912138789)
                  ·
                    rfl

theorem cell22_1967954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_1967954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1967954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1967954 prefixEnd_1967954 := by exact prefixLift 1967954
  have htrace : WordTrace (prefixWord ++ tailWord_1967954) baseStart_1967954 baseEnd_1967954 := by
    simpa [prefixWord, tailWord_1967954, baseEnd_1967954] using wordTrace_append hprefix tailTrace_1967954
  have hstable : (prefixWord ++ tailWord_1967954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1967954).length < 2 ^ (prefixWord ++ tailWord_1967954).sum := by decide
  have hdescent : baseEnd_1967954 < baseStart_1967954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1967954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968025 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 2, 5]
def baseStart_1968025 : Nat := 118140960795 + 1968025 * 2 ^ 59
def prefixEnd_1968025 : Nat := 4983230072969 + 3 ^ 40 * 1968025 * 2
def baseEnd_1968025 : Nat := 673695176709845217891149

theorem tailTrace_1968025 : CollatzResearch.WordTrace tailWord_1968025 prefixEnd_1968025 673695176709845217891149 := by
  unfold tailWord_1968025
  simp only [CollatzResearch.WordTrace]
  refine ⟨71779768695189011755873529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47853179130126007837249019 71779768695189011755873529)
  ·
    refine ⟨53834826521391758816905147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71779768695189011755873529 53834826521391758816905147)
    ·
      refine ⟨80752239782087638225357721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53834826521391758816905147 80752239782087638225357721)
      ·
        refine ⟨60564179836565728669018291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80752239782087638225357721 60564179836565728669018291)
        ·
          refine ⟨90846269754848593003527437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60564179836565728669018291 90846269754848593003527437)
          ·
            refine ⟨34067351158068222376322789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90846269754848593003527437 34067351158068222376322789)
            ·
              refine ⟨6387628342137791695560523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34067351158068222376322789 6387628342137791695560523)
              ·
                refine ⟨9581442513206687543340785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6387628342137791695560523 9581442513206687543340785)
                ·
                  refine ⟨7186081884905015657505589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9581442513206687543340785 7186081884905015657505589)
                  ·
                    refine ⟨673695176709845217891149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7186081884905015657505589 673695176709845217891149)
                    ·
                      rfl

theorem cell22_1968025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 5].length) (baseStart_1968025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968025 prefixEnd_1968025 := by exact prefixLift 1968025
  have htrace : WordTrace (prefixWord ++ tailWord_1968025) baseStart_1968025 baseEnd_1968025 := by
    simpa [prefixWord, tailWord_1968025, baseEnd_1968025] using wordTrace_append hprefix tailTrace_1968025
  have hstable : (prefixWord ++ tailWord_1968025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968025).length < 2 ^ (prefixWord ++ tailWord_1968025).sum := by decide
  have hdescent : baseEnd_1968025 < baseStart_1968025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968057 : List Nat := [1, 2, 1, 4, 2, 1, 1, 5, 1, 4]
def baseStart_1968057 : Nat := 118140960795 + 1968057 * 2 ^ 59
def prefixEnd_1968057 : Nat := 4983230072969 + 3 ^ 40 * 1968057 * 2
def baseEnd_1968057 : Nat := 673706130963807801091051

theorem tailTrace_1968057 : CollatzResearch.WordTrace tailWord_1968057 prefixEnd_1968057 673706130963807801091051 := by
  unfold tailWord_1968057
  simp only [CollatzResearch.WordTrace]
  refine ⟨71780935831073081221038425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47853957220715387480692283 71780935831073081221038425)
  ·
    refine ⟨53835701873304810915778819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71780935831073081221038425 53835701873304810915778819)
    ·
      refine ⟨80753552809957216373668229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53835701873304810915778819 80753552809957216373668229)
      ·
        refine ⟨15141291151866978070062793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80753552809957216373668229 15141291151866978070062793)
        ·
          refine ⟨11355968363900233552547095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15141291151866978070062793 11355968363900233552547095)
          ·
            refine ⟨17033952545850350328820643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11355968363900233552547095 17033952545850350328820643)
            ·
              refine ⟨25550928818775525493230965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17033952545850350328820643 25550928818775525493230965)
              ·
                refine ⟨2395399576760205514990403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25550928818775525493230965 2395399576760205514990403)
                ·
                  refine ⟨3593099365140308272485605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2395399576760205514990403 3593099365140308272485605)
                  ·
                    refine ⟨673706130963807801091051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3593099365140308272485605 673706130963807801091051)
                    ·
                      rfl

theorem cell22_1968057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_1968057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968057 prefixEnd_1968057 := by exact prefixLift 1968057
  have htrace : WordTrace (prefixWord ++ tailWord_1968057) baseStart_1968057 baseEnd_1968057 := by
    simpa [prefixWord, tailWord_1968057, baseEnd_1968057] using wordTrace_append hprefix tailTrace_1968057
  have hstable : (prefixWord ++ tailWord_1968057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968057).length < 2 ^ (prefixWord ++ tailWord_1968057).sum := by decide
  have hdescent : baseEnd_1968057 < baseStart_1968057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968072 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 6]
def baseStart_1968072 : Nat := 118140960795 + 1968072 * 2 ^ 59
def prefixEnd_1968072 : Nat := 4983230072969 + 3 ^ 40 * 1968072 * 2
def baseEnd_1968072 : Nat := 224570421923450920655335

theorem tailTrace_1968072 : CollatzResearch.WordTrace tailWord_1968072 prefixEnd_1968072 224570421923450920655335 := by
  unfold tailWord_1968072
  simp only [CollatzResearch.WordTrace]
  refine ⟨35890741463009369391417235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47854321950679159188556313 35890741463009369391417235)
  ·
    refine ⟨53836112194514054087125853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35890741463009369391417235 53836112194514054087125853)
    ·
      refine ⟨20188542072942770282672195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53836112194514054087125853 20188542072942770282672195)
      ·
        refine ⟨30282813109414155424008293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20188542072942770282672195 30282813109414155424008293)
        ·
          refine ⟨5678027458015154142001555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30282813109414155424008293 5678027458015154142001555)
          ·
            refine ⟨8517041187022731213002333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5678027458015154142001555 8517041187022731213002333)
            ·
              refine ⟨3193890445133524204875875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8517041187022731213002333 3193890445133524204875875)
              ·
                refine ⟨4790835667700286307313813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3193890445133524204875875 4790835667700286307313813)
                ·
                  refine ⟨224570421923450920655335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4790835667700286307313813 224570421923450920655335)
                  ·
                    rfl

theorem cell22_1968072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 6].length) (baseStart_1968072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968072 prefixEnd_1968072 := by exact prefixLift 1968072
  have htrace : WordTrace (prefixWord ++ tailWord_1968072) baseStart_1968072 baseEnd_1968072 := by
    simpa [prefixWord, tailWord_1968072, baseEnd_1968072] using wordTrace_append hprefix tailTrace_1968072
  have hstable : (prefixWord ++ tailWord_1968072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968072).length < 2 ^ (prefixWord ++ tailWord_1968072).sum := by decide
  have hdescent : baseEnd_1968072 < baseStart_1968072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968100 : List Nat := [2, 3, 1, 1, 1, 1, 3, 10]
def baseStart_1968100 : Nat := 118140960795 + 1968100 * 2 ^ 59
def prefixEnd_1968100 : Nat := 4983230072969 + 3 ^ 40 * 1968100 * 2
def baseEnd_1968100 : Nat := 74857872304730002473991

theorem tailTrace_1968100 : CollatzResearch.WordTrace tailWord_1968100 prefixEnd_1968100 74857872304730002473991 := by
  unfold tailWord_1968100
  simp only [CollatzResearch.WordTrace]
  refine ⟨35891252084958649782426877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47855002779944866376569169 35891252084958649782426877)
  ·
    refine ⟨13459219531859493668410079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35891252084958649782426877 13459219531859493668410079)
    ·
      refine ⟨20188829297789240502615119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13459219531859493668410079 20188829297789240502615119)
      ·
        refine ⟨30283243946683860753922679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20188829297789240502615119 30283243946683860753922679)
        ·
          refine ⟨45424865920025791130884019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30283243946683860753922679 45424865920025791130884019)
          ·
            refine ⟨68137298880038686696326029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45424865920025791130884019 68137298880038686696326029)
            ·
              refine ⟨25551487080014507511122261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68137298880038686696326029 25551487080014507511122261)
              ·
                refine ⟨74857872304730002473991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25551487080014507511122261 74857872304730002473991)
                ·
                  rfl

theorem cell22_1968100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 10].length) (baseStart_1968100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968100 prefixEnd_1968100 := by exact prefixLift 1968100
  have htrace : WordTrace (prefixWord ++ tailWord_1968100) baseStart_1968100 baseEnd_1968100 := by
    simpa [prefixWord, tailWord_1968100, baseEnd_1968100] using wordTrace_append hprefix tailTrace_1968100
  have hstable : (prefixWord ++ tailWord_1968100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968100).length < 2 ^ (prefixWord ++ tailWord_1968100).sum := by decide
  have hdescent : baseEnd_1968100 < baseStart_1968100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968145 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 11]
def baseStart_1968145 : Nat := 118140960795 + 1968145 * 2 ^ 59
def prefixEnd_1968145 : Nat := 4983230072969 + 3 ^ 40 * 1968145 * 2
def baseEnd_1968145 : Nat := 224578751720734968296927

theorem tailTrace_1968145 : CollatzResearch.WordTrace tailWord_1968145 prefixEnd_1968145 224578751720734968296927 := by
  unfold tailWord_1968145
  simp only [CollatzResearch.WordTrace]
  refine ⟨71784145454754272250241889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47856096969836181500161259 71784145454754272250241889)
  ·
    refine ⟨53838109091065704187681417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71784145454754272250241889 53838109091065704187681417)
    ·
      refine ⟨40378581818299278140761063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53838109091065704187681417 40378581818299278140761063)
      ·
        refine ⟨60567872727448917211141595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40378581818299278140761063 60567872727448917211141595)
        ·
          refine ⟨90851809091173375816712393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60567872727448917211141595 90851809091173375816712393)
          ·
            refine ⟨68138856818380031862534295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90851809091173375816712393 68138856818380031862534295)
            ·
              refine ⟨102208285227570047793801443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68138856818380031862534295 102208285227570047793801443)
              ·
                refine ⟨153312427841355071690702165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102208285227570047793801443 153312427841355071690702165)
                ·
                  refine ⟨224578751720734968296927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 153312427841355071690702165 224578751720734968296927)
                  ·
                    rfl

theorem cell22_1968145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 11].length) (baseStart_1968145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968145 prefixEnd_1968145 := by exact prefixLift 1968145
  have htrace : WordTrace (prefixWord ++ tailWord_1968145) baseStart_1968145 baseEnd_1968145 := by
    simpa [prefixWord, tailWord_1968145, baseEnd_1968145] using wordTrace_append hprefix tailTrace_1968145
  have hstable : (prefixWord ++ tailWord_1968145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968145).length < 2 ^ (prefixWord ++ tailWord_1968145).sum := by decide
  have hdescent : baseEnd_1968145 < baseStart_1968145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968162 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 7]
def baseStart_1968162 : Nat := 118140960795 + 1968162 * 2 ^ 59
def prefixEnd_1968162 : Nat := 4983230072969 + 3 ^ 40 * 1968162 * 2
def baseEnd_1968162 : Nat := 224580691536540842405243

theorem tailTrace_1968162 : CollatzResearch.WordTrace tailWord_1968162 prefixEnd_1968162 224580691536540842405243 := by
  unfold tailWord_1968162
  simp only [CollatzResearch.WordTrace]
  refine ⟨17946191373923171038402685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47856510330461789435740493 17946191373923171038402685)
  ·
    refine ⟨6729821765221189139401007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17946191373923171038402685 6729821765221189139401007)
    ·
      refine ⟨10094732647831783709101511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6729821765221189139401007 10094732647831783709101511)
      ·
        refine ⟨15142098971747675563652267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10094732647831783709101511 15142098971747675563652267)
        ·
          refine ⟨22713148457621513345478401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15142098971747675563652267 22713148457621513345478401)
          ·
            refine ⟨17034861343216135009108801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22713148457621513345478401 17034861343216135009108801)
            ·
              refine ⟨12776146007412101256831601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17034861343216135009108801 12776146007412101256831601)
              ·
                refine ⟨9582109505559075942623701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12776146007412101256831601 9582109505559075942623701)
                ·
                  refine ⟨224580691536540842405243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9582109505559075942623701 224580691536540842405243)
                  ·
                    rfl

theorem cell22_1968162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_1968162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968162 prefixEnd_1968162 := by exact prefixLift 1968162
  have htrace : WordTrace (prefixWord ++ tailWord_1968162) baseStart_1968162 baseEnd_1968162 := by
    simpa [prefixWord, tailWord_1968162, baseEnd_1968162] using wordTrace_append hprefix tailTrace_1968162
  have hstable : (prefixWord ++ tailWord_1968162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968162).length < 2 ^ (prefixWord ++ tailWord_1968162).sum := by decide
  have hdescent : baseEnd_1968162 < baseStart_1968162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968177 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 2, 5]
def baseStart_1968177 : Nat := 118140960795 + 1968177 * 2 ^ 59
def prefixEnd_1968177 : Nat := 4983230072969 + 3 ^ 40 * 1968177 * 2
def baseEnd_1968177 : Nat := 673747209416167488090683

theorem tailTrace_1968177 : CollatzResearch.WordTrace tailWord_1968177 prefixEnd_1968177 673747209416167488090683 := by
  unfold tailWord_1968177
  simp only [CollatzResearch.WordTrace]
  refine ⟨71785312590638341715406785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47856875060425561143604523 71785312590638341715406785)
  ·
    refine ⟨53838984442978756286555089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71785312590638341715406785 53838984442978756286555089)
    ·
      refine ⟨40379238332234067214916317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53838984442978756286555089 40379238332234067214916317)
      ·
        refine ⟨15142214374587775205593619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40379238332234067214916317 15142214374587775205593619)
        ·
          refine ⟨22713321561881662808390429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15142214374587775205593619 22713321561881662808390429)
          ·
            refine ⟨8517495585705623553146411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22713321561881662808390429 8517495585705623553146411)
            ·
              refine ⟨12776243378558435329719617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8517495585705623553146411 12776243378558435329719617)
              ·
                refine ⟨9582182533918826497289713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12776243378558435329719617 9582182533918826497289713)
                ·
                  refine ⟨7186636900439119872967285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9582182533918826497289713 7186636900439119872967285)
                  ·
                    refine ⟨673747209416167488090683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7186636900439119872967285 673747209416167488090683)
                    ·
                      rfl

theorem cell22_1968177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_1968177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968177 prefixEnd_1968177 := by exact prefixLift 1968177
  have htrace : WordTrace (prefixWord ++ tailWord_1968177) baseStart_1968177 baseEnd_1968177 := by
    simpa [prefixWord, tailWord_1968177, baseEnd_1968177] using wordTrace_append hprefix tailTrace_1968177
  have hstable : (prefixWord ++ tailWord_1968177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968177).length < 2 ^ (prefixWord ++ tailWord_1968177).sum := by decide
  have hdescent : baseEnd_1968177 < baseStart_1968177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968239 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 4, 3]
def baseStart_1968239 : Nat := 118140960795 + 1968239 * 2 ^ 59
def prefixEnd_1968239 : Nat := 4983230072969 + 3 ^ 40 * 1968239 * 2
def baseEnd_1968239 : Nat := 673768433283219993040493

theorem tailTrace_1968239 : CollatzResearch.WordTrace tailWord_1968239 prefixEnd_1968239 673768433283219993040493 := by
  unfold tailWord_1968239
  simp only [CollatzResearch.WordTrace]
  refine ⟨71787573916413726304163771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47858382610942484202775847 71787573916413726304163771)
  ·
    refine ⟨107681360874620589456245657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71787573916413726304163771 107681360874620589456245657)
    ·
      refine ⟨80761020655965442092184243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107681360874620589456245657 80761020655965442092184243)
      ·
        refine ⟨121141530983948163138276365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80761020655965442092184243 121141530983948163138276365)
        ·
          refine ⟨45428074118980561176853637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121141530983948163138276365 45428074118980561176853637)
          ·
            refine ⟨8517763897308855220660057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45428074118980561176853637 8517763897308855220660057)
            ·
              refine ⟨6388322922981641415495043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8517763897308855220660057 6388322922981641415495043)
              ·
                refine ⟨9582484384472462123242565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388322922981641415495043 9582484384472462123242565)
                ·
                  refine ⟨1796715822088586648107981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9582484384472462123242565 1796715822088586648107981)
                  ·
                    refine ⟨673768433283219993040493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1796715822088586648107981 673768433283219993040493)
                    ·
                      rfl

theorem cell22_1968239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 3].length) (baseStart_1968239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968239 prefixEnd_1968239 := by exact prefixLift 1968239
  have htrace : WordTrace (prefixWord ++ tailWord_1968239) baseStart_1968239 baseEnd_1968239 := by
    simpa [prefixWord, tailWord_1968239, baseEnd_1968239] using wordTrace_append hprefix tailTrace_1968239
  have hstable : (prefixWord ++ tailWord_1968239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968239).length < 2 ^ (prefixWord ++ tailWord_1968239).sum := by decide
  have hdescent : baseEnd_1968239 < baseStart_1968239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968241 : List Nat := [1, 2, 2, 2, 1, 1, 7, 2, 4]
def baseStart_1968241 : Nat := 118140960795 + 1968241 * 2 ^ 59
def prefixEnd_1968241 : Nat := 4983230072969 + 3 ^ 40 * 1968241 * 2
def baseEnd_1968241 : Nat := 224589705974697551496829

theorem tailTrace_1968241 : CollatzResearch.WordTrace tailWord_1968241 prefixEnd_1968241 224589705974697551496829 := by
  unfold tailWord_1968241
  simp only [CollatzResearch.WordTrace]
  refine ⟨71787646862406480645736577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47858431241604320430491051 71787646862406480645736577)
  ·
    refine ⟨53840735146804860484302433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71787646862406480645736577 53840735146804860484302433)
    ·
      refine ⟨40380551360103645363226825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53840735146804860484302433 40380551360103645363226825)
      ·
        refine ⟨30285413520077734022420119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40380551360103645363226825 30285413520077734022420119)
        ·
          refine ⟨45428120280116601033630179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30285413520077734022420119 45428120280116601033630179)
          ·
            refine ⟨68142180420174901550445269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45428120280116601033630179 68142180420174901550445269)
            ·
              refine ⟨1597082353597849255088561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 68142180420174901550445269 1597082353597849255088561)
              ·
                refine ⟨1197811765198386941316421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597082353597849255088561 1197811765198386941316421)
                ·
                  refine ⟨224589705974697551496829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1197811765198386941316421 224589705974697551496829)
                  ·
                    rfl

theorem cell22_1968241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 4].length) (baseStart_1968241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968241 prefixEnd_1968241 := by exact prefixLift 1968241
  have htrace : WordTrace (prefixWord ++ tailWord_1968241) baseStart_1968241 baseEnd_1968241 := by
    simpa [prefixWord, tailWord_1968241, baseEnd_1968241] using wordTrace_append hprefix tailTrace_1968241
  have hstable : (prefixWord ++ tailWord_1968241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968241).length < 2 ^ (prefixWord ++ tailWord_1968241).sum := by decide
  have hdescent : baseEnd_1968241 < baseStart_1968241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968252 : List Nat := [2, 2, 2, 1, 1, 4, 1, 9]
def baseStart_1968252 : Nat := 118140960795 + 1968252 * 2 ^ 59
def prefixEnd_1968252 : Nat := 4983230072969 + 3 ^ 40 * 1968252 * 2
def baseEnd_1968252 : Nat := 74863653716543588051717

theorem tailTrace_1968252 : CollatzResearch.WordTrace tailWord_1968252 prefixEnd_1968252 74863653716543588051717 := by
  unfold tailWord_1968252
  simp only [CollatzResearch.WordTrace]
  refine ⟨35894024032683314762193505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47858698710244419682924673 35894024032683314762193505)
  ·
    refine ⟨26920518024512486071645129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35894024032683314762193505 26920518024512486071645129)
    ·
      refine ⟨20190388518384364553733847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26920518024512486071645129 20190388518384364553733847)
      ·
        refine ⟨30285582777576546830600771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20190388518384364553733847 30285582777576546830600771)
        ·
          refine ⟨45428374166364820245901157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30285582777576546830600771 45428374166364820245901157)
          ·
            refine ⟨8517820156193403796106467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45428374166364820245901157 8517820156193403796106467)
            ·
              refine ⟨12776730234290105694159701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8517820156193403796106467 12776730234290105694159701)
              ·
                refine ⟨74863653716543588051717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12776730234290105694159701 74863653716543588051717)
                ·
                  rfl

theorem cell22_1968252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 9].length) (baseStart_1968252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968252 prefixEnd_1968252 := by exact prefixLift 1968252
  have htrace : WordTrace (prefixWord ++ tailWord_1968252) baseStart_1968252 baseEnd_1968252 := by
    simpa [prefixWord, tailWord_1968252, baseEnd_1968252] using wordTrace_append hprefix tailTrace_1968252
  have hstable : (prefixWord ++ tailWord_1968252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968252).length < 2 ^ (prefixWord ++ tailWord_1968252).sum := by decide
  have hdescent : baseEnd_1968252 < baseStart_1968252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968286 : List Nat := [4, 3, 1, 1, 4, 9]
def baseStart_1968286 : Nat := 118140960795 + 1968286 * 2 ^ 59
def prefixEnd_1968286 : Nat := 4983230072969 + 3 ^ 40 * 1968286 * 2
def baseEnd_1968286 : Nat := 8318327436342315273029

theorem tailTrace_1968286 : CollatzResearch.WordTrace tailWord_1968286 prefixEnd_1968286 8318327436342315273029 := by
  unfold tailWord_1968286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8973661018405431666390589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47859525431495635554083141 8973661018405431666390589)
  ·
    refine ⟨3365122881902036874896471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8973661018405431666390589 3365122881902036874896471)
    ·
      refine ⟨5047684322853055312344707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3365122881902036874896471 5047684322853055312344707)
      ·
        refine ⟨7571526484279582968517061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5047684322853055312344707 7571526484279582968517061)
        ·
          refine ⟨1419661215802421806596949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7571526484279582968517061 1419661215802421806596949)
          ·
            refine ⟨8318327436342315273029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1419661215802421806596949 8318327436342315273029)
            ·
              rfl

theorem cell22_1968286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 9].length) (baseStart_1968286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968286 prefixEnd_1968286 := by exact prefixLift 1968286
  have htrace : WordTrace (prefixWord ++ tailWord_1968286) baseStart_1968286 baseEnd_1968286 := by
    simpa [prefixWord, tailWord_1968286, baseEnd_1968286] using wordTrace_append hprefix tailTrace_1968286
  have hstable : (prefixWord ++ tailWord_1968286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968286).length < 2 ^ (prefixWord ++ tailWord_1968286).sum := by decide
  have hdescent : baseEnd_1968286 < baseStart_1968286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968314 : List Nat := [3, 1, 1, 1, 2, 2, 4, 3, 5]
def baseStart_1968314 : Nat := 118140960795 + 1968314 * 2 ^ 59
def prefixEnd_1968314 : Nat := 4983230072969 + 3 ^ 40 * 1968314 * 2
def baseEnd_1968314 : Nat := 224598035771981599138421

theorem tailTrace_1968314 : CollatzResearch.WordTrace tailWord_1968314 prefixEnd_1968314 224598035771981599138421 := by
  unfold tailWord_1968314
  simp only [CollatzResearch.WordTrace]
  refine ⟨17947577347785503528285999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47860206260761342742095997 17947577347785503528285999)
  ·
    refine ⟨26921366021678255292428999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17947577347785503528285999 26921366021678255292428999)
    ·
      refine ⟨40382049032517382938643499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26921366021678255292428999 40382049032517382938643499)
      ·
        refine ⟨60573073548776074407965249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40382049032517382938643499 60573073548776074407965249)
        ·
          refine ⟨45429805161582055805973937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60573073548776074407965249 45429805161582055805973937)
          ·
            refine ⟨34072353871186541854480453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45429805161582055805973937 34072353871186541854480453)
            ·
              refine ⟨6388566350847476597715085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34072353871186541854480453 6388566350847476597715085)
              ·
                refine ⟨2395712381567803724143157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6388566350847476597715085 2395712381567803724143157)
                ·
                  refine ⟨224598035771981599138421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2395712381567803724143157 224598035771981599138421)
                  ·
                    rfl

theorem cell22_1968314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_1968314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968314 prefixEnd_1968314 := by exact prefixLift 1968314
  have htrace : WordTrace (prefixWord ++ tailWord_1968314) baseStart_1968314 baseEnd_1968314 := by
    simpa [prefixWord, tailWord_1968314, baseEnd_1968314] using wordTrace_append hprefix tailTrace_1968314
  have hstable : (prefixWord ++ tailWord_1968314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968314).length < 2 ^ (prefixWord ++ tailWord_1968314).sum := by decide
  have hdescent : baseEnd_1968314 < baseStart_1968314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968318 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_1968318 : Nat := 118140960795 + 1968318 * 2 ^ 59
def prefixEnd_1968318 : Nat := 4983230072969 + 3 ^ 40 * 1968318 * 2
def baseEnd_1968318 : Nat := 673795476597690120315251

theorem tailTrace_1968318 : CollatzResearch.WordTrace tailWord_1968318 prefixEnd_1968318 673795476597690120315251 := by
  unfold tailWord_1968318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8973806910390940349536201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47860303522085015197526405 8973806910390940349536201)
  ·
    refine ⟨6730355182793205262152151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8973806910390940349536201 6730355182793205262152151)
    ·
      refine ⟨10095532774189807893228227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6730355182793205262152151 10095532774189807893228227)
      ·
        refine ⟨15143299161284711839842341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10095532774189807893228227 15143299161284711839842341)
        ·
          refine ⟨2839368592740883469970439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15143299161284711839842341 2839368592740883469970439)
          ·
            refine ⟨4259052889111325204955659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839368592740883469970439 4259052889111325204955659)
            ·
              refine ⟨6388579333666987807433489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4259052889111325204955659 6388579333666987807433489)
              ·
                refine ⟨4791434500250240855575117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6388579333666987807433489 4791434500250240855575117)
                ·
                  refine ⟨1796787937593840320840669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4791434500250240855575117 1796787937593840320840669)
                  ·
                    refine ⟨673795476597690120315251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1796787937593840320840669 673795476597690120315251)
                    ·
                      rfl

theorem cell22_1968318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_1968318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968318 prefixEnd_1968318 := by exact prefixLift 1968318
  have htrace : WordTrace (prefixWord ++ tailWord_1968318) baseStart_1968318 baseEnd_1968318 := by
    simpa [prefixWord, tailWord_1968318, baseEnd_1968318] using wordTrace_append hprefix tailTrace_1968318
  have hstable : (prefixWord ++ tailWord_1968318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968318).length < 2 ^ (prefixWord ++ tailWord_1968318).sum := by decide
  have hdescent : baseEnd_1968318 < baseStart_1968318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968348 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 7]
def baseStart_1968348 : Nat := 118140960795 + 1968348 * 2 ^ 59
def prefixEnd_1968348 : Nat := 4983230072969 + 3 ^ 40 * 1968348 * 2
def baseEnd_1968348 : Nat := 224601915403593347355053

theorem tailTrace_1968348 : CollatzResearch.WordTrace tailWord_1968348 prefixEnd_1968348 224601915403593347355053 := by
  unfold tailWord_1968348
  simp only [CollatzResearch.WordTrace]
  refine ⟨35895774736509418959940849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47861032982012558613254465 35895774736509418959940849)
  ·
    refine ⟨26921831052382064219955637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35895774736509418959940849 26921831052382064219955637)
    ·
      refine ⟨2523921661160818520620841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26921831052382064219955637 2523921661160818520620841)
      ·
        refine ⟨1892941245870613890465631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2523921661160818520620841 1892941245870613890465631)
        ·
          refine ⟨2839411868805920835698447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1892941245870613890465631 2839411868805920835698447)
          ·
            refine ⟨4259117803208881253547671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839411868805920835698447 4259117803208881253547671)
            ·
              refine ⟨6388676704813321880321507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4259117803208881253547671 6388676704813321880321507)
              ·
                refine ⟨9583015057219982820482261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6388676704813321880321507 9583015057219982820482261)
                ·
                  refine ⟨224601915403593347355053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9583015057219982820482261 224601915403593347355053)
                  ·
                    rfl

theorem cell22_1968348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_1968348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968348 prefixEnd_1968348 := by exact prefixLift 1968348
  have htrace : WordTrace (prefixWord ++ tailWord_1968348) baseStart_1968348 baseEnd_1968348 := by
    simpa [prefixWord, tailWord_1968348, baseEnd_1968348] using wordTrace_append hprefix tailTrace_1968348
  have hstable : (prefixWord ++ tailWord_1968348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968348).length < 2 ^ (prefixWord ++ tailWord_1968348).sum := by decide
  have hdescent : baseEnd_1968348 < baseStart_1968348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968393 : List Nat := [1, 2, 1, 1, 3, 6, 1, 3, 4]
def baseStart_1968393 : Nat := 118140960795 + 1968393 * 2 ^ 59
def prefixEnd_1968393 : Nat := 4983230072969 + 3 ^ 40 * 1968393 * 2
def baseEnd_1968393 : Nat := 224607050210138308230007

theorem tailTrace_1968393 : CollatzResearch.WordTrace tailWord_1968393 prefixEnd_1968393 224607050210138308230007 := by
  unfold tailWord_1968393
  simp only [CollatzResearch.WordTrace]
  refine ⟨71793190757855810605269833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47862127171903873736846555 71793190757855810605269833)
  ·
    refine ⟨53844893068391857953952375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71793190757855810605269833 53844893068391857953952375)
    ·
      refine ⟨80767339602587786930928563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53844893068391857953952375 80767339602587786930928563)
      ·
        refine ⟨121151009403881680396392845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80767339602587786930928563 121151009403881680396392845)
        ·
          refine ⟨45431628526455630148647317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121151009403881680396392845 45431628526455630148647317)
          ·
            refine ⟨2129607587177607663217843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45431628526455630148647317 2129607587177607663217843)
            ·
              refine ⟨3194411380766411494826765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2129607587177607663217843 3194411380766411494826765)
              ·
                refine ⟨1197904267787404310560037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3194411380766411494826765 1197904267787404310560037)
                ·
                  refine ⟨224607050210138308230007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1197904267787404310560037 224607050210138308230007)
                  ·
                    rfl

theorem cell22_1968393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 4].length) (baseStart_1968393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968393 prefixEnd_1968393 := by exact prefixLift 1968393
  have htrace : WordTrace (prefixWord ++ tailWord_1968393) baseStart_1968393 baseEnd_1968393 := by
    simpa [prefixWord, tailWord_1968393, baseEnd_1968393] using wordTrace_append hprefix tailTrace_1968393
  have hstable : (prefixWord ++ tailWord_1968393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968393).length < 2 ^ (prefixWord ++ tailWord_1968393).sum := by decide
  have hdescent : baseEnd_1968393 < baseStart_1968393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968410 : List Nat := [3, 1, 1, 3, 4, 1, 3, 2, 4]
def baseStart_1968410 : Nat := 118140960795 + 1968410 * 2 ^ 59
def prefixEnd_1968410 : Nat := 4983230072969 + 3 ^ 40 * 1968410 * 2
def baseEnd_1968410 : Nat := 224608990025944182338323

theorem tailTrace_1968410 : CollatzResearch.WordTrace tailWord_1968410 prefixEnd_1968410 224608990025944182338323 := by
  unfold tailWord_1968410
  simp only [CollatzResearch.WordTrace]
  refine ⟨17948452699698555627159671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47862540532529481672425789 17948452699698555627159671)
  ·
    refine ⟨26922679049547833440739507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17948452699698555627159671 26922679049547833440739507)
    ·
      refine ⟨40384018574321750161109261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26922679049547833440739507 40384018574321750161109261)
      ·
        refine ⟨15144006965370656310415973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40384018574321750161109261 15144006965370656310415973)
        ·
          refine ⟨2839501306006998058202995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15144006965370656310415973 2839501306006998058202995)
          ·
            refine ⟨4259251959010497087304493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839501306006998058202995 4259251959010497087304493)
            ·
              refine ⟨1597219484628936407739185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4259251959010497087304493 1597219484628936407739185)
              ·
                refine ⟨1197914613471702305804389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597219484628936407739185 1197914613471702305804389)
                ·
                  refine ⟨224608990025944182338323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1197914613471702305804389 224608990025944182338323)
                  ·
                    rfl

theorem cell22_1968410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_1968410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968410 prefixEnd_1968410 := by exact prefixLift 1968410
  have htrace : WordTrace (prefixWord ++ tailWord_1968410) baseStart_1968410 baseEnd_1968410 := by
    simpa [prefixWord, tailWord_1968410, baseEnd_1968410] using wordTrace_append hprefix tailTrace_1968410
  have hstable : (prefixWord ++ tailWord_1968410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968410).length < 2 ^ (prefixWord ++ tailWord_1968410).sum := by decide
  have hdescent : baseEnd_1968410 < baseStart_1968410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968421 : List Nat := [1, 3, 1, 2, 5, 1, 2, 7]
def baseStart_1968421 : Nat := 118140960795 + 1968421 * 2 ^ 59
def prefixEnd_1968421 : Nat := 4983230072969 + 3 ^ 40 * 1968421 * 2
def baseEnd_1968421 : Nat := 74870081733625798332215

theorem tailTrace_1968421 : CollatzResearch.WordTrace tailWord_1968421 prefixEnd_1968421 74870081733625798332215 := by
  unfold tailWord_1968421
  simp only [CollatzResearch.WordTrace]
  refine ⟨71794212001754371387289117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47862808001169580924859411 71794212001754371387289117)
  ·
    refine ⟨26922829500657889270233419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71794212001754371387289117 26922829500657889270233419)
    ·
      refine ⟨40384244250986833905350129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26922829500657889270233419 40384244250986833905350129)
      ·
        refine ⟨30288183188240125429012597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40384244250986833905350129 30288183188240125429012597)
        ·
          refine ⟨2839517173897511758969931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30288183188240125429012597 2839517173897511758969931)
          ·
            refine ⟨4259275760846267638454897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2839517173897511758969931 4259275760846267638454897)
            ·
              refine ⟨3194456820634700728841173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4259275760846267638454897 3194456820634700728841173)
              ·
                refine ⟨74870081733625798332215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3194456820634700728841173 74870081733625798332215)
                ·
                  rfl

theorem cell22_1968421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 7].length) (baseStart_1968421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968421 prefixEnd_1968421 := by exact prefixLift 1968421
  have htrace : WordTrace (prefixWord ++ tailWord_1968421) baseStart_1968421 baseEnd_1968421 := by
    simpa [prefixWord, tailWord_1968421, baseEnd_1968421] using wordTrace_append hprefix tailTrace_1968421
  have hstable : (prefixWord ++ tailWord_1968421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968421).length < 2 ^ (prefixWord ++ tailWord_1968421).sum := by decide
  have hdescent : baseEnd_1968421 < baseStart_1968421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968466 : List Nat := [3, 2, 2, 1, 1, 1, 3, 4, 5]
def baseStart_1968466 : Nat := 118140960795 + 1968466 * 2 ^ 59
def prefixEnd_1968466 : Nat := 4983230072969 + 3 ^ 40 * 1968466 * 2
def baseEnd_1968466 : Nat := 224615380007422355871599

theorem tailTrace_1968466 : CollatzResearch.WordTrace tailWord_1968466 prefixEnd_1968466 224615380007422355871599 := by
  unfold tailWord_1968466
  simp only [CollatzResearch.WordTrace]
  refine ⟨17948963321647836018169313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47863902191060896048451501 17948963321647836018169313)
  ·
    refine ⟨13461722491235877013626985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17948963321647836018169313 13461722491235877013626985)
    ·
      refine ⟨10096291868426907760220239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13461722491235877013626985 10096291868426907760220239)
      ·
        refine ⟨15144437802640361640330359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10096291868426907760220239 15144437802640361640330359)
        ·
          refine ⟨22716656703960542460495539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15144437802640361640330359 22716656703960542460495539)
          ·
            refine ⟨34074985055940813690743309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22716656703960542460495539 34074985055940813690743309)
            ·
              refine ⟨12778119395977805134028741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34074985055940813690743309 12778119395977805134028741)
              ·
                refine ⟨2395897386745838462630389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12778119395977805134028741 2395897386745838462630389)
                ·
                  refine ⟨224615380007422355871599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2395897386745838462630389 224615380007422355871599)
                  ·
                    rfl

theorem cell22_1968466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_1968466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968466 prefixEnd_1968466 := by exact prefixLift 1968466
  have htrace : WordTrace (prefixWord ++ tailWord_1968466) baseStart_1968466 baseEnd_1968466 := by
    simpa [prefixWord, tailWord_1968466, baseEnd_1968466] using wordTrace_append hprefix tailTrace_1968466
  have hstable : (prefixWord ++ tailWord_1968466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968466).length < 2 ^ (prefixWord ++ tailWord_1968466).sum := by decide
  have hdescent : baseEnd_1968466 < baseStart_1968466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968496 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 3, 4]
def baseStart_1968496 : Nat := 118140960795 + 1968496 * 2 ^ 59
def prefixEnd_1968496 : Nat := 4983230072969 + 3 ^ 40 * 1968496 * 2
def baseEnd_1968496 : Nat := 673856409635356989364705

theorem tailTrace_1968496 : CollatzResearch.WordTrace tailWord_1968496 prefixEnd_1968496 673856409635356989364705 := by
  unfold tailWord_1968496
  simp only [CollatzResearch.WordTrace]
  refine ⟨35898473738241329598134671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47864631650988439464179561 35898473738241329598134671)
  ·
    refine ⟨53847710607361994397202007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35898473738241329598134671 53847710607361994397202007)
    ·
      refine ⟨80771565911042991595803011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53847710607361994397202007 80771565911042991595803011)
      ·
        refine ⟨121157348866564487393704517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80771565911042991595803011 121157348866564487393704517)
        ·
          refine ⟨22717002912480841386319597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121157348866564487393704517 22717002912480841386319597)
          ·
            refine ⟨8518876092180315519869849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22717002912480841386319597 8518876092180315519869849)
            ·
              refine ⟨6389157069135236639902387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8518876092180315519869849 6389157069135236639902387)
              ·
                refine ⟨9583735603702854959853581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6389157069135236639902387 9583735603702854959853581)
                ·
                  refine ⟨3593900851388570609945093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9583735603702854959853581 3593900851388570609945093)
                  ·
                    refine ⟨673856409635356989364705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3593900851388570609945093 673856409635356989364705)
                    ·
                      rfl

theorem cell22_1968496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_1968496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968496 prefixEnd_1968496 := by exact prefixLift 1968496
  have htrace : WordTrace (prefixWord ++ tailWord_1968496) baseStart_1968496 baseEnd_1968496 := by
    simpa [prefixWord, tailWord_1968496, baseEnd_1968496] using wordTrace_append hprefix tailTrace_1968496
  have hstable : (prefixWord ++ tailWord_1968496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968496).length < 2 ^ (prefixWord ++ tailWord_1968496).sum := by decide
  have hdescent : baseEnd_1968496 < baseStart_1968496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968586 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 2, 6]
def baseStart_1968586 : Nat := 118140960795 + 1968586 * 2 ^ 59
def prefixEnd_1968586 : Nat := 4983230072969 + 3 ^ 40 * 1968586 * 2
def baseEnd_1968586 : Nat := 673887218474626754614429

theorem tailTrace_1968586 : CollatzResearch.WordTrace tailWord_1968586 prefixEnd_1968586 673887218474626754614429 := by
  unfold tailWord_1968586
  simp only [CollatzResearch.WordTrace]
  refine ⟨17950057511539151141761403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47866820030771069711363741 17950057511539151141761403)
  ·
    refine ⟨26925086267308726712642105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17950057511539151141761403 26925086267308726712642105)
    ·
      refine ⟨20193814700481545034481579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26925086267308726712642105 20193814700481545034481579)
      ·
        refine ⟨30290722050722317551722369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20193814700481545034481579 30290722050722317551722369)
        ·
          refine ⟨22718041538041738163791777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30290722050722317551722369 22718041538041738163791777)
          ·
            refine ⟨17038531153531303622843833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22718041538041738163791777 17038531153531303622843833)
            ·
              refine ⟨12778898365148477717132875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17038531153531303622843833 12778898365148477717132875)
              ·
                refine ⟨19168347547722716575699313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12778898365148477717132875 19168347547722716575699313)
                ·
                  refine ⟨14376260660792037431774485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19168347547722716575699313 14376260660792037431774485)
                  ·
                    refine ⟨673887218474626754614429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14376260660792037431774485 673887218474626754614429)
                    ·
                      rfl

theorem cell22_1968586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_1968586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968586 prefixEnd_1968586 := by exact prefixLift 1968586
  have htrace : WordTrace (prefixWord ++ tailWord_1968586) baseStart_1968586 baseEnd_1968586 := by
    simpa [prefixWord, tailWord_1968586, baseEnd_1968586] using wordTrace_append hprefix tailTrace_1968586
  have hstable : (prefixWord ++ tailWord_1968586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968586).length < 2 ^ (prefixWord ++ tailWord_1968586).sum := by decide
  have hdescent : baseEnd_1968586 < baseStart_1968586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968682 : List Nat := [3, 1, 4, 1, 1, 2, 4, 1, 1, 4]
def baseStart_1968682 : Nat := 118140960795 + 1968682 * 2 ^ 59
def prefixEnd_1968682 : Nat := 4983230072969 + 3 ^ 40 * 1968682 * 2
def baseEnd_1968682 : Nat := 673920081236514504214135

theorem tailTrace_1968682 : CollatzResearch.WordTrace tailWord_1968682 prefixEnd_1968682 673920081236514504214135 := by
  unfold tailWord_1968682
  simp only [CollatzResearch.WordTrace]
  refine ⟨17950932863452203240635075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47869154302539208641693533 17950932863452203240635075)
  ·
    refine ⟨26926399295178304860952613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17950932863452203240635075 26926399295178304860952613)
    ·
      refine ⟨5048699867845932161428615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26926399295178304860952613 5048699867845932161428615)
      ·
        refine ⟨7573049801768898242142923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5048699867845932161428615 7573049801768898242142923)
        ·
          refine ⟨11359574702653347363214385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7573049801768898242142923 11359574702653347363214385)
          ·
            refine ⟨8519681026990010522410789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11359574702653347363214385 8519681026990010522410789)
            ·
              refine ⟨1597440192560626972952023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8519681026990010522410789 1597440192560626972952023)
              ·
                refine ⟨2396160288840940459428035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597440192560626972952023 2396160288840940459428035)
                ·
                  refine ⟨3594240433261410689142053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396160288840940459428035 3594240433261410689142053)
                  ·
                    refine ⟨673920081236514504214135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3594240433261410689142053 673920081236514504214135)
                    ·
                      rfl

theorem cell22_1968682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_1968682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968682 prefixEnd_1968682 := by exact prefixLift 1968682
  have htrace : WordTrace (prefixWord ++ tailWord_1968682) baseStart_1968682 baseEnd_1968682 := by
    simpa [prefixWord, tailWord_1968682, baseEnd_1968682] using wordTrace_append hprefix tailTrace_1968682
  have hstable : (prefixWord ++ tailWord_1968682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968682).length < 2 ^ (prefixWord ++ tailWord_1968682).sum := by decide
  have hdescent : baseEnd_1968682 < baseStart_1968682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968691 : List Nat := [1, 1, 1, 2, 4, 2, 11]
def baseStart_1968691 : Nat := 118140960795 + 1968691 * 2 ^ 59
def prefixEnd_1968691 : Nat := 4983230072969 + 3 ^ 40 * 1968691 * 2
def baseEnd_1968691 : Nat := 24960117115571906694041

theorem tailTrace_1968691 : CollatzResearch.WordTrace tailWord_1968691 prefixEnd_1968691 24960117115571906694041 := by
  unfold tailWord_1968691
  simp only [CollatzResearch.WordTrace]
  refine ⟨71804059710776207499617927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47869373140517471666411951 71804059710776207499617927)
  ·
    refine ⟨107706089566164311249426891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71804059710776207499617927 107706089566164311249426891)
    ·
      refine ⟨161559134349246466874140337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107706089566164311249426891 161559134349246466874140337)
      ·
        refine ⟨121169350761934850155605253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161559134349246466874140337 121169350761934850155605253)
        ·
          refine ⟨22719253267862784404175985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121169350761934850155605253 22719253267862784404175985)
          ·
            refine ⟨17039439950897088303131989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22719253267862784404175985 17039439950897088303131989)
            ·
              refine ⟨24960117115571906694041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17039439950897088303131989 24960117115571906694041)
              ·
                rfl

theorem cell22_1968691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 11].length) (baseStart_1968691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968691 prefixEnd_1968691 := by exact prefixLift 1968691
  have htrace : WordTrace (prefixWord ++ tailWord_1968691) baseStart_1968691 baseEnd_1968691 := by
    simpa [prefixWord, tailWord_1968691, baseEnd_1968691] using wordTrace_append hprefix tailTrace_1968691
  have hstable : (prefixWord ++ tailWord_1968691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968691).length < 2 ^ (prefixWord ++ tailWord_1968691).sum := by decide
  have hdescent : baseEnd_1968691 < baseStart_1968691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968693 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_1968693 : Nat := 118140960795 + 1968693 * 2 ^ 59
def prefixEnd_1968693 : Nat := 4983230072969 + 3 ^ 40 * 1968693 * 2
def baseEnd_1968693 : Nat := 673923846761314142189101

theorem tailTrace_1968693 : CollatzResearch.WordTrace tailWord_1968693 prefixEnd_1968693 673923846761314142189101 := by
  unfold tailWord_1968693
  simp only [CollatzResearch.WordTrace]
  refine ⟨71804132656768961841190733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47869421771179307894127155 71804132656768961841190733)
  ·
    refine ⟨26926549746288360690446525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71804132656768961841190733 26926549746288360690446525)
    ·
      refine ⟨10097456154858135258917447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26926549746288360690446525 10097456154858135258917447)
      ·
        refine ⟨15146184232287202888376171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10097456154858135258917447 15146184232287202888376171)
        ·
          refine ⟨22719276348430804332564257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15146184232287202888376171 22719276348430804332564257)
          ·
            refine ⟨17039457261323103249423193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22719276348430804332564257 17039457261323103249423193)
            ·
              refine ⟨12779592945992327437067395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17039457261323103249423193 12779592945992327437067395)
              ·
                refine ⟨19169389418988491155601093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12779592945992327437067395 19169389418988491155601093)
                ·
                  refine ⟨3594260516060342091675205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19169389418988491155601093 3594260516060342091675205)
                  ·
                    refine ⟨673923846761314142189101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3594260516060342091675205 673923846761314142189101)
                    ·
                      rfl

theorem cell22_1968693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_1968693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968693 prefixEnd_1968693 := by exact prefixLift 1968693
  have htrace : WordTrace (prefixWord ++ tailWord_1968693) baseStart_1968693 baseEnd_1968693 := by
    simpa [prefixWord, tailWord_1968693, baseEnd_1968693] using wordTrace_append hprefix tailTrace_1968693
  have hstable : (prefixWord ++ tailWord_1968693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968693).length < 2 ^ (prefixWord ++ tailWord_1968693).sum := by decide
  have hdescent : baseEnd_1968693 < baseStart_1968693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968783 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 3, 4]
def baseStart_1968783 : Nat := 118140960795 + 1968783 * 2 ^ 59
def prefixEnd_1968783 : Nat := 4983230072969 + 3 ^ 40 * 1968783 * 2
def baseEnd_1968783 : Nat := 673954655600583907438825

theorem tailTrace_1968783 : CollatzResearch.WordTrace tailWord_1968783 prefixEnd_1968783 673954655600583907438825 := by
  unfold tailWord_1968783
  simp only [CollatzResearch.WordTrace]
  refine ⟨71807415226442907211967003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47871610150961938141311335 71807415226442907211967003)
  ·
    refine ⟨107711122839664360817950505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71807415226442907211967003 107711122839664360817950505)
    ·
      refine ⟨80783342129748270613462879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107711122839664360817950505 80783342129748270613462879)
      ·
        refine ⟨121175013194622405920194319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80783342129748270613462879 121175013194622405920194319)
        ·
          refine ⟨181762519791933608880291479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121175013194622405920194319 181762519791933608880291479)
          ·
            refine ⟨272643779687900413320437219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181762519791933608880291479 272643779687900413320437219)
            ·
              refine ⟨408965669531850619980655829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272643779687900413320437219 408965669531850619980655829)
              ·
                refine ⟨9585132879652748905796621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 408965669531850619980655829 9585132879652748905796621)
                ·
                  refine ⟨3594424829869780839673733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9585132879652748905796621 3594424829869780839673733)
                  ·
                    refine ⟨673954655600583907438825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3594424829869780839673733 673954655600583907438825)
                    ·
                      rfl

theorem cell22_1968783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_1968783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968783 prefixEnd_1968783 := by exact prefixLift 1968783
  have htrace : WordTrace (prefixWord ++ tailWord_1968783) baseStart_1968783 baseEnd_1968783 := by
    simpa [prefixWord, tailWord_1968783, baseEnd_1968783] using wordTrace_append hprefix tailTrace_1968783
  have hstable : (prefixWord ++ tailWord_1968783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968783).length < 2 ^ (prefixWord ++ tailWord_1968783).sum := by decide
  have hdescent : baseEnd_1968783 < baseStart_1968783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968873 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 1, 8]
def baseStart_1968873 : Nat := 118140960795 + 1968873 * 2 ^ 59
def prefixEnd_1968873 : Nat := 4983230072969 + 3 ^ 40 * 1968873 * 2
def baseEnd_1968873 : Nat := 673985464439853672688549

theorem tailTrace_1968873 : CollatzResearch.WordTrace tailWord_1968873 prefixEnd_1968873 673985464439853672688549 := by
  unfold tailWord_1968873
  simp only [CollatzResearch.WordTrace]
  refine ⟨71810697796116852582743273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47873798530744568388495515 71810697796116852582743273)
  ·
    refine ⟨53858023347087639437057455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71810697796116852582743273 53858023347087639437057455)
    ·
      refine ⟨80787035020631459155586183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53858023347087639437057455 80787035020631459155586183)
      ·
        refine ⟨121180552530947188733379275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80787035020631459155586183 121180552530947188733379275)
        ·
          refine ⟨181770828796420783100068913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121180552530947188733379275 181770828796420783100068913)
          ·
            refine ⟨136328121597315587325051685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181770828796420783100068913 136328121597315587325051685)
            ·
              refine ⟨25561522799496672623447191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 136328121597315587325051685 25561522799496672623447191)
              ·
                refine ⟨38342284199245008935170787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25561522799496672623447191 38342284199245008935170787)
                ·
                  refine ⟨57513426298867513402756181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38342284199245008935170787 57513426298867513402756181)
                  ·
                    refine ⟨673985464439853672688549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57513426298867513402756181 673985464439853672688549)
                    ·
                      rfl

theorem cell22_1968873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_1968873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968873 prefixEnd_1968873 := by exact prefixLift 1968873
  have htrace : WordTrace (prefixWord ++ tailWord_1968873) baseStart_1968873 baseEnd_1968873 := by
    simpa [prefixWord, tailWord_1968873, baseEnd_1968873] using wordTrace_append hprefix tailTrace_1968873
  have hstable : (prefixWord ++ tailWord_1968873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968873).length < 2 ^ (prefixWord ++ tailWord_1968873).sum := by decide
  have hdescent : baseEnd_1968873 < baseStart_1968873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968892 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 3, 3]
def baseStart_1968892 : Nat := 118140960795 + 1968892 * 2 ^ 59
def prefixEnd_1968892 : Nat := 4983230072969 + 3 ^ 40 * 1968892 * 2
def baseEnd_1968892 : Nat := 673991968528143956463491

theorem tailTrace_1968892 : CollatzResearch.WordTrace tailWord_1968892 prefixEnd_1968892 673991968528143956463491 := by
  unfold tailWord_1968892
  simp only [CollatzResearch.WordTrace]
  refine ⟨35905695391524009413842465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47874260522032012551789953 35905695391524009413842465)
  ·
    refine ⟨26929271543643007060381849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35905695391524009413842465 26929271543643007060381849)
    ·
      refine ⟨20196953657732255295286387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26929271543643007060381849 20196953657732255295286387)
      ·
        refine ⟨30295430486598382942929581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20196953657732255295286387 30295430486598382942929581)
        ·
          refine ⟨11360786432474393603598593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30295430486598382942929581 11360786432474393603598593)
          ·
            refine ⟨8520589824355795202698945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11360786432474393603598593 8520589824355795202698945)
            ·
              refine ⟨6390442368266846402024209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8520589824355795202698945 6390442368266846402024209)
              ·
                refine ⟨4792831776200134801518157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6390442368266846402024209 4792831776200134801518157)
                ·
                  refine ⟨1797311916075050550569309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4792831776200134801518157 1797311916075050550569309)
                  ·
                    refine ⟨673991968528143956463491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1797311916075050550569309 673991968528143956463491)
                    ·
                      rfl

theorem cell22_1968892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_1968892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968892 prefixEnd_1968892 := by exact prefixLift 1968892
  have htrace : WordTrace (prefixWord ++ tailWord_1968892) baseStart_1968892 baseEnd_1968892 := by
    simpa [prefixWord, tailWord_1968892, baseEnd_1968892] using wordTrace_append hprefix tailTrace_1968892
  have hstable : (prefixWord ++ tailWord_1968892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968892).length < 2 ^ (prefixWord ++ tailWord_1968892).sum := by decide
  have hdescent : baseEnd_1968892 < baseStart_1968892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968894 : List Nat := [4, 2, 2, 1, 2, 3, 2, 6]
def baseStart_1968894 : Nat := 118140960795 + 1968894 * 2 ^ 59
def prefixEnd_1968894 : Nat := 4983230072969 + 3 ^ 40 * 1968894 * 2
def baseEnd_1968894 : Nat := 74888072574335179768165

theorem tailTrace_1968894 : CollatzResearch.WordTrace tailWord_1968894 prefixEnd_1968894 74888072574335179768165 := by
  unfold tailWord_1968894
  simp only [CollatzResearch.WordTrace]
  refine ⟨8976432966130096646157217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47874309152693848779505157 8976432966130096646157217)
  ·
    refine ⟨6732324724597572484617913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8976432966130096646157217 6732324724597572484617913)
    ·
      refine ⟨5049243543448179363463435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6732324724597572484617913 5049243543448179363463435)
      ·
        refine ⟨7573865315172269045195153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5049243543448179363463435 7573865315172269045195153)
        ·
          refine ⟨5680398986379201783896365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7573865315172269045195153 5680398986379201783896365)
          ·
            refine ⟨2130149619892200668961137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5680398986379201783896365 2130149619892200668961137)
            ·
              refine ⟨1597612214919150501720853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130149619892200668961137 1597612214919150501720853)
              ·
                refine ⟨74888072574335179768165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1597612214919150501720853 74888072574335179768165)
                ·
                  rfl

theorem cell22_1968894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_1968894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968894 prefixEnd_1968894 := by exact prefixLift 1968894
  have htrace : WordTrace (prefixWord ++ tailWord_1968894) baseStart_1968894 baseEnd_1968894 := by
    simpa [prefixWord, tailWord_1968894, baseEnd_1968894] using wordTrace_append hprefix tailTrace_1968894
  have hstable : (prefixWord ++ tailWord_1968894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968894).length < 2 ^ (prefixWord ++ tailWord_1968894).sum := by decide
  have hdescent : baseEnd_1968894 < baseStart_1968894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968967 : List Nat := [1, 1, 4, 1, 2, 1, 1, 7, 4]
def baseStart_1968967 : Nat := 118140960795 + 1968967 * 2 ^ 59
def prefixEnd_1968967 : Nat := 4983230072969 + 3 ^ 40 * 1968967 * 2
def baseEnd_1968967 : Nat := 224672547520289586946087

theorem tailTrace_1968967 : CollatzResearch.WordTrace tailWord_1968967 prefixEnd_1968967 224672547520289586946087 := by
  unfold tailWord_1968967
  simp only [CollatzResearch.WordTrace]
  refine ⟨71814126257776306636665155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47876084171850871091110103 71814126257776306636665155)
  ·
    refine ⟨107721189386664459954997733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71814126257776306636665155 107721189386664459954997733)
    ·
      refine ⟨20197723009999586241562075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107721189386664459954997733 20197723009999586241562075)
      ·
        refine ⟨30296584514999379362343113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20197723009999586241562075 30296584514999379362343113)
        ·
          refine ⟨22722438386249534521757335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30296584514999379362343113 22722438386249534521757335)
          ·
            refine ⟨34083657579374301782636003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22722438386249534521757335 34083657579374301782636003)
            ·
              refine ⟨51125486369061452673954005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34083657579374301782636003 51125486369061452673954005)
              ·
                refine ⟨1198253586774877797045797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51125486369061452673954005 1198253586774877797045797)
                ·
                  refine ⟨224672547520289586946087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1198253586774877797045797 224672547520289586946087)
                  ·
                    rfl

theorem cell22_1968967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 4].length) (baseStart_1968967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968967 prefixEnd_1968967 := by exact prefixLift 1968967
  have htrace : WordTrace (prefixWord ++ tailWord_1968967) baseStart_1968967 baseEnd_1968967 := by
    simpa [prefixWord, tailWord_1968967, baseEnd_1968967] using wordTrace_append hprefix tailTrace_1968967
  have hstable : (prefixWord ++ tailWord_1968967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968967).length < 2 ^ (prefixWord ++ tailWord_1968967).sum := by decide
  have hdescent : baseEnd_1968967 < baseStart_1968967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968969 : List Nat := [1, 2, 1, 1, 2, 6, 3, 1, 1, 4]
def baseStart_1968969 : Nat := 118140960795 + 1968969 * 2 ^ 59
def prefixEnd_1968969 : Nat := 4983230072969 + 3 ^ 40 * 1968969 * 2
def baseEnd_1968969 : Nat := 674018327201741422288255

theorem tailTrace_1968969 : CollatzResearch.WordTrace tailWord_1968969 prefixEnd_1968969 674018327201741422288255 := by
  unfold tailWord_1968969
  simp only [CollatzResearch.WordTrace]
  refine ⟨71814199203769060978237961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47876132802512707318825307 71814199203769060978237961)
  ·
    refine ⟨53860649402826795733678471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71814199203769060978237961 53860649402826795733678471)
    ·
      refine ⟨80790974104240193600517707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53860649402826795733678471 80790974104240193600517707)
      ·
        refine ⟨121186461156360290400776561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80790974104240193600517707 121186461156360290400776561)
        ·
          refine ⟨90889845867270217800582421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121186461156360290400776561 90889845867270217800582421)
          ·
            refine ⟨4260461525028291459402301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90889845867270217800582421 4260461525028291459402301)
            ·
              refine ⟨1597673071885609297275863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4260461525028291459402301 1597673071885609297275863)
              ·
                refine ⟨2396509607828413945913795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1597673071885609297275863 2396509607828413945913795)
                ·
                  refine ⟨3594764411742620918870693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2396509607828413945913795 3594764411742620918870693)
                  ·
                    refine ⟨674018327201741422288255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3594764411742620918870693 674018327201741422288255)
                    ·
                      rfl

theorem cell22_1968969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 1, 4].length) (baseStart_1968969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968969 prefixEnd_1968969 := by exact prefixLift 1968969
  have htrace : WordTrace (prefixWord ++ tailWord_1968969) baseStart_1968969 baseEnd_1968969 := by
    simpa [prefixWord, tailWord_1968969, baseEnd_1968969] using wordTrace_append hprefix tailTrace_1968969
  have hstable : (prefixWord ++ tailWord_1968969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968969).length < 2 ^ (prefixWord ++ tailWord_1968969).sum := by decide
  have hdescent : baseEnd_1968969 < baseStart_1968969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1968999 : List Nat := [1, 1, 5, 1, 2, 2, 2, 3, 2, 3]
def baseStart_1968999 : Nat := 118140960795 + 1968999 * 2 ^ 59
def prefixEnd_1968999 : Nat := 4983230072969 + 3 ^ 40 * 1968999 * 2
def baseEnd_1968999 : Nat := 674028596814831344038163

theorem tailTrace_1968999 : CollatzResearch.WordTrace tailWord_1968999 prefixEnd_1968999 674028596814831344038163 := by
  unfold tailWord_1968999
  simp only [CollatzResearch.WordTrace]
  refine ⟨71815293393660376101830051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47876862262440250734553367 71815293393660376101830051)
  ·
    refine ⟨107722940090490564152745077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71815293393660376101830051 107722940090490564152745077)
    ·
      refine ⟨10099025633483490389319851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107722940090490564152745077 10099025633483490389319851)
      ·
        refine ⟨15148538450225235583979777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10099025633483490389319851 15148538450225235583979777)
        ·
          refine ⟨11361403837668926687984833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15148538450225235583979777 11361403837668926687984833)
          ·
            refine ⟨8521052878251695015988625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11361403837668926687984833 8521052878251695015988625)
            ·
              refine ⟨6390789658688771261991469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8521052878251695015988625 6390789658688771261991469)
              ·
                refine ⟨2396546122008289223246801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6390789658688771261991469 2396546122008289223246801)
                ·
                  refine ⟨1797409591506216917435101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2396546122008289223246801 1797409591506216917435101)
                  ·
                    refine ⟨674028596814831344038163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1797409591506216917435101 674028596814831344038163)
                    ·
                      rfl

theorem cell22_1968999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_1968999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1968999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1968999 prefixEnd_1968999 := by exact prefixLift 1968999
  have htrace : WordTrace (prefixWord ++ tailWord_1968999) baseStart_1968999 baseEnd_1968999 := by
    simpa [prefixWord, tailWord_1968999, baseEnd_1968999] using wordTrace_append hprefix tailTrace_1968999
  have hstable : (prefixWord ++ tailWord_1968999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1968999).length < 2 ^ (prefixWord ++ tailWord_1968999).sum := by decide
  have hdescent : baseEnd_1968999 < baseStart_1968999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1968999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969014 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_1969014 : Nat := 118140960795 + 1969014 * 2 ^ 59
def prefixEnd_1969014 : Nat := 4983230072969 + 3 ^ 40 * 1969014 * 2
def baseEnd_1969014 : Nat := 674033731621376304913117

theorem tailTrace_1969014 : CollatzResearch.WordTrace tailWord_1969014 prefixEnd_1969014 674033731621376304913117 := by
  unfold tailWord_1969014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4488490030537877103976631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47877226992404022442417397 4488490030537877103976631)
  ·
    refine ⟨6732735045806815655964947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4488490030537877103976631 6732735045806815655964947)
    ·
      refine ⟨10099102568710223483947421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6732735045806815655964947 10099102568710223483947421)
      ·
        refine ⟨3787163463266333806480283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10099102568710223483947421 3787163463266333806480283)
        ·
          refine ⟨5680745194899500709720425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787163463266333806480283 5680745194899500709720425)
          ·
            refine ⟨4260558896174625532290319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5680745194899500709720425 4260558896174625532290319)
            ·
              refine ⟨6390838344261938298435479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4260558896174625532290319 6390838344261938298435479)
              ·
                refine ⟨9586257516392907447653219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6390838344261938298435479 9586257516392907447653219)
                ·
                  refine ⟨14379386274589361171479829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9586257516392907447653219 14379386274589361171479829)
                  ·
                    refine ⟨674033731621376304913117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14379386274589361171479829 674033731621376304913117)
                    ·
                      rfl

theorem cell22_1969014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_1969014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969014 prefixEnd_1969014 := by exact prefixLift 1969014
  have htrace : WordTrace (prefixWord ++ tailWord_1969014) baseStart_1969014 baseEnd_1969014 := by
    simpa [prefixWord, tailWord_1969014, baseEnd_1969014] using wordTrace_append hprefix tailTrace_1969014
  have hstable : (prefixWord ++ tailWord_1969014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969014).length < 2 ^ (prefixWord ++ tailWord_1969014).sum := by decide
  have hdescent : baseEnd_1969014 < baseStart_1969014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969027 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 5, 3]
def baseStart_1969027 : Nat := 118140960795 + 1969027 * 2 ^ 59
def prefixEnd_1969027 : Nat := 4983230072969 + 3 ^ 40 * 1969027 * 2
def baseEnd_1969027 : Nat := 674038181787048604338077

theorem tailTrace_1969027 : CollatzResearch.WordTrace tailWord_1969027 prefixEnd_1969027 674038181787048604338077 := by
  unfold tailWord_1969027
  simp only [CollatzResearch.WordTrace]
  refine ⟨71816314637558936883849335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47877543091705957922566223 71816314637558936883849335)
  ·
    refine ⟨107724471956338405325774003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71816314637558936883849335 107724471956338405325774003)
    ·
      refine ⟨161586707934507607988661005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107724471956338405325774003 161586707934507607988661005)
      ·
        refine ⟨60595015475440352995747877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 161586707934507607988661005 60595015475440352995747877)
        ·
          refine ⟨11361565401645066186702727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60595015475440352995747877 11361565401645066186702727)
          ·
            refine ⟨17042348102467599280054091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11361565401645066186702727 17042348102467599280054091)
            ·
              refine ⟨25563522153701398920081137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17042348102467599280054091 25563522153701398920081137)
              ·
                refine ⟨19172641615276049190060853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25563522153701398920081137 19172641615276049190060853)
                ·
                  refine ⟨1797435151432129611568205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19172641615276049190060853 1797435151432129611568205)
                  ·
                    refine ⟨674038181787048604338077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1797435151432129611568205 674038181787048604338077)
                    ·
                      rfl

theorem cell22_1969027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 3].length) (baseStart_1969027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969027 prefixEnd_1969027 := by exact prefixLift 1969027
  have htrace : WordTrace (prefixWord ++ tailWord_1969027) baseStart_1969027 baseEnd_1969027 := by
    simpa [prefixWord, tailWord_1969027, baseEnd_1969027] using wordTrace_append hprefix tailTrace_1969027
  have hstable : (prefixWord ++ tailWord_1969027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969027).length < 2 ^ (prefixWord ++ tailWord_1969027).sum := by decide
  have hdescent : baseEnd_1969027 < baseStart_1969027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969153 : List Nat := [1, 2, 4, 1, 2, 4, 2, 2, 4]
def baseStart_1969153 : Nat := 118140960795 + 1969153 * 2 ^ 59
def prefixEnd_1969153 : Nat := 4983230072969 + 3 ^ 40 * 1969153 * 2
def baseEnd_1969153 : Nat := 224693771387342091895897

theorem tailTrace_1969153 : CollatzResearch.WordTrace tailWord_1969153 prefixEnd_1969153 224693771387342091895897 := by
  unfold tailWord_1969153
  simp only [CollatzResearch.WordTrace]
  refine ⟨71820910235102460402936113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47880606823401640268624075 71820910235102460402936113)
  ·
    refine ⟨53865682676326845302202085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71820910235102460402936113 53865682676326845302202085)
    ·
      refine ⟨10099815501811283494162891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53865682676326845302202085 10099815501811283494162891)
      ·
        refine ⟨15149723252716925241244337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10099815501811283494162891 15149723252716925241244337)
        ·
          refine ⟨11362292439537693930933253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15149723252716925241244337 11362292439537693930933253)
          ·
            refine ⟨2130429832413317612049985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11362292439537693930933253 2130429832413317612049985)
            ·
              refine ⟨1597822374309988209037489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130429832413317612049985 1597822374309988209037489)
              ·
                refine ⟨1198366780732491156778117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597822374309988209037489 1198366780732491156778117)
                ·
                  refine ⟨224693771387342091895897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1198366780732491156778117 224693771387342091895897)
                  ·
                    rfl

theorem cell22_1969153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 4].length) (baseStart_1969153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969153 prefixEnd_1969153 := by exact prefixLift 1969153
  have htrace : WordTrace (prefixWord ++ tailWord_1969153) baseStart_1969153 baseEnd_1969153 := by
    simpa [prefixWord, tailWord_1969153, baseEnd_1969153] using wordTrace_append hprefix tailTrace_1969153
  have hstable : (prefixWord ++ tailWord_1969153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969153).length < 2 ^ (prefixWord ++ tailWord_1969153).sum := by decide
  have hdescent : baseEnd_1969153 < baseStart_1969153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969164 : List Nat := [2, 2, 1, 2, 3, 4, 1, 7]
def baseStart_1969164 : Nat := 118140960795 + 1969164 * 2 ^ 59
def prefixEnd_1969164 : Nat := 4983230072969 + 3 ^ 40 * 1969164 * 2
def baseEnd_1969164 : Nat := 74898342187425101518073

theorem tailTrace_1969164 : CollatzResearch.WordTrace tailWord_1969164 prefixEnd_1969164 74898342187425101518073 := by
  unfold tailWord_1969164
  simp only [CollatzResearch.WordTrace]
  refine ⟨35910655719031304640793273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47880874292041739521057697 35910655719031304640793273)
  ·
    refine ⟨26932991789273478480594955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35910655719031304640793273 26932991789273478480594955)
    ·
      refine ⟨40399487683910217720892433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26932991789273478480594955 40399487683910217720892433)
      ·
        refine ⟨30299615762932663290669325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40399487683910217720892433 30299615762932663290669325)
        ·
          refine ⟨11362355911099748734000997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30299615762932663290669325 11362355911099748734000997)
          ·
            refine ⟨2130441733331202887625187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11362355911099748734000997 2130441733331202887625187)
            ·
              refine ⟨3195662599996804331437781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130441733331202887625187 3195662599996804331437781)
              ·
                refine ⟨74898342187425101518073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3195662599996804331437781 74898342187425101518073)
                ·
                  rfl

theorem cell22_1969164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 7].length) (baseStart_1969164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969164 prefixEnd_1969164 := by exact prefixLift 1969164
  have htrace : WordTrace (prefixWord ++ tailWord_1969164) baseStart_1969164 baseEnd_1969164 := by
    simpa [prefixWord, tailWord_1969164, baseEnd_1969164] using wordTrace_append hprefix tailTrace_1969164
  have hstable : (prefixWord ++ tailWord_1969164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969164).length < 2 ^ (prefixWord ++ tailWord_1969164).sum := by decide
  have hdescent : baseEnd_1969164 < baseStart_1969164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969181 : List Nat := [1, 4, 2, 2, 3, 1, 3, 6]
def baseStart_1969181 : Nat := 118140960795 + 1969181 * 2 ^ 59
def prefixEnd_1969181 : Nat := 4983230072969 + 3 ^ 40 * 1969181 * 2
def baseEnd_1969181 : Nat := 74898988792693726220845

theorem tailTrace_1969181 : CollatzResearch.WordTrace tailWord_1969181 prefixEnd_1969181 74898988792693726220845 := by
  unfold tailWord_1969181
  simp only [CollatzResearch.WordTrace]
  refine ⟨71821931479001021184955397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47881287652667347456636931 71821931479001021184955397)
  ·
    refine ⟨13466612152312691472179137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71821931479001021184955397 13466612152312691472179137)
    ·
      refine ⟨10099959114234518604134353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13466612152312691472179137 10099959114234518604134353)
      ·
        refine ⟨7574969335675888953100765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10099959114234518604134353 7574969335675888953100765)
        ·
          refine ⟨2840613500878458357412787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7574969335675888953100765 2840613500878458357412787)
          ·
            refine ⟨4260920251317687536119181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2840613500878458357412787 4260920251317687536119181)
            ·
              refine ⟨1597845094244132826044693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4260920251317687536119181 1597845094244132826044693)
              ·
                refine ⟨74898988792693726220845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1597845094244132826044693 74898988792693726220845)
                ·
                  rfl

theorem cell22_1969181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 6].length) (baseStart_1969181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969181 prefixEnd_1969181 := by exact prefixLift 1969181
  have htrace : WordTrace (prefixWord ++ tailWord_1969181) baseStart_1969181 baseEnd_1969181 := by
    simpa [prefixWord, tailWord_1969181, baseEnd_1969181] using wordTrace_append hprefix tailTrace_1969181
  have hstable : (prefixWord ++ tailWord_1969181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969181).length < 2 ^ (prefixWord ++ tailWord_1969181).sum := by decide
  have hdescent : baseEnd_1969181 < baseStart_1969181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969209 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 7]
def baseStart_1969209 : Nat := 118140960795 + 1969209 * 2 ^ 59
def prefixEnd_1969209 : Nat := 4983230072969 + 3 ^ 40 * 1969209 * 2
def baseEnd_1969209 : Nat := 224700161368820265429173

theorem tailTrace_1969209 : CollatzResearch.WordTrace tailWord_1969209 prefixEnd_1969209 224700161368820265429173 := by
  unfold tailWord_1969209
  simp only [CollatzResearch.WordTrace]
  refine ⟨71822952722899581966974681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47881968481933054644649787 71822952722899581966974681)
  ·
    refine ⟨53867214542174686475231011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71822952722899581966974681 53867214542174686475231011)
    ·
      refine ⟨80800821813262029712846517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53867214542174686475231011 80800821813262029712846517)
      ·
        refine ⟨7575077044993315285579361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80800821813262029712846517 7575077044993315285579361)
        ·
          refine ⟨5681307783744986464184521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7575077044993315285579361 5681307783744986464184521)
          ·
            refine ⟨4260980837808739848138391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5681307783744986464184521 4260980837808739848138391)
            ·
              refine ⟨6391471256713109772207587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4260980837808739848138391 6391471256713109772207587)
              ·
                refine ⟨9587206885069664658311381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6391471256713109772207587 9587206885069664658311381)
                ·
                  refine ⟨224700161368820265429173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9587206885069664658311381 224700161368820265429173)
                  ·
                    rfl

theorem cell22_1969209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_1969209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969209 prefixEnd_1969209 := by exact prefixLift 1969209
  have htrace : WordTrace (prefixWord ++ tailWord_1969209) baseStart_1969209 baseEnd_1969209 := by
    simpa [prefixWord, tailWord_1969209, baseEnd_1969209] using wordTrace_append hprefix tailTrace_1969209
  have hstable : (prefixWord ++ tailWord_1969209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969209).length < 2 ^ (prefixWord ++ tailWord_1969209).sum := by decide
  have hdescent : baseEnd_1969209 < baseStart_1969209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969213 : List Nat := [1, 4, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_1969213 : Nat := 118140960795 + 1969213 * 2 ^ 59
def prefixEnd_1969213 : Nat := 4983230072969 + 3 ^ 40 * 1969213 * 2
def baseEnd_1969213 : Nat := 674101853388206119187507

theorem tailTrace_1969213 : CollatzResearch.WordTrace tailWord_1969213 prefixEnd_1969213 674101853388206119187507 := by
  unfold tailWord_1969213
  simp only [CollatzResearch.WordTrace]
  refine ⟨71823098614885090650120293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47882065743256727100080195 71823098614885090650120293)
  ·
    refine ⟨13466830990290954496897555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71823098614885090650120293 13466830990290954496897555)
    ·
      refine ⟨20200246485436431745346333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13466830990290954496897555 20200246485436431745346333)
      ·
        refine ⟨7575092432038661904504875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20200246485436431745346333 7575092432038661904504875)
        ·
          refine ⟨11362638648057992856757313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7575092432038661904504875 11362638648057992856757313)
          ·
            refine ⟨8521978986043494642567985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11362638648057992856757313 8521978986043494642567985)
            ·
              refine ⟨6391484239532620981925989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8521978986043494642567985 6391484239532620981925989)
              ·
                refine ⟨1198403294912366434111123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6391484239532620981925989 1198403294912366434111123)
                ·
                  refine ⟨1797604942368549651166685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198403294912366434111123 1797604942368549651166685)
                  ·
                    refine ⟨674101853388206119187507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1797604942368549651166685 674101853388206119187507)
                    ·
                      rfl

theorem cell22_1969213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_1969213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969213 prefixEnd_1969213 := by exact prefixLift 1969213
  have htrace : WordTrace (prefixWord ++ tailWord_1969213) baseStart_1969213 baseEnd_1969213 := by
    simpa [prefixWord, tailWord_1969213, baseEnd_1969213] using wordTrace_append hprefix tailTrace_1969213
  have hstable : (prefixWord ++ tailWord_1969213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969213).length < 2 ^ (prefixWord ++ tailWord_1969213).sum := by decide
  have hdescent : baseEnd_1969213 < baseStart_1969213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969267 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 2, 10]
def baseStart_1969267 : Nat := 118140960795 + 1969267 * 2 ^ 59
def prefixEnd_1969267 : Nat := 4983230072969 + 3 ^ 40 * 1969267 * 2
def baseEnd_1969267 : Nat := 674120338691767978337341

theorem tailTrace_1969267 : CollatzResearch.WordTrace tailWord_1969267 prefixEnd_1969267 674120338691767978337341 := by
  unfold tailWord_1969267
  simp only [CollatzResearch.WordTrace]
  refine ⟨71825068156689457872586055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47883378771126305248390703 71825068156689457872586055)
  ·
    refine ⟨107737602235034186808879083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71825068156689457872586055 107737602235034186808879083)
    ·
      refine ⟨161606403352551280213318625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107737602235034186808879083 161606403352551280213318625)
      ·
        refine ⟨121204802514413460159988969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161606403352551280213318625 121204802514413460159988969)
        ·
          refine ⟨90903601885810095119991727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121204802514413460159988969 90903601885810095119991727)
          ·
            refine ⟨136355402828715142679987591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90903601885810095119991727 136355402828715142679987591)
            ·
              refine ⟨204533104243072714019981387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 136355402828715142679987591 204533104243072714019981387)
              ·
                refine ⟨306799656364609071029972081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204533104243072714019981387 306799656364609071029972081)
                ·
                  refine ⟨230099742273456803272479061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 306799656364609071029972081 230099742273456803272479061)
                  ·
                    refine ⟨674120338691767978337341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 230099742273456803272479061 674120338691767978337341)
                    ·
                      rfl

theorem cell22_1969267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 10].length) (baseStart_1969267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969267 prefixEnd_1969267 := by exact prefixLift 1969267
  have htrace : WordTrace (prefixWord ++ tailWord_1969267) baseStart_1969267 baseEnd_1969267 := by
    simpa [prefixWord, tailWord_1969267, baseEnd_1969267] using wordTrace_append hprefix tailTrace_1969267
  have hstable : (prefixWord ++ tailWord_1969267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969267).length < 2 ^ (prefixWord ++ tailWord_1969267).sum := by decide
  have hdescent : baseEnd_1969267 < baseStart_1969267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969322 : List Nat := [3, 1, 5, 1, 1, 3, 2, 2, 4]
def baseStart_1969322 : Nat := 118140960795 + 1969322 * 2 ^ 59
def prefixEnd_1969322 : Nat := 4983230072969 + 3 ^ 40 * 1969322 * 2
def baseEnd_1969322 : Nat := 224713055438588722737391

theorem tailTrace_1969322 : CollatzResearch.WordTrace tailWord_1969322 prefixEnd_1969322 224713055438588722737391 := by
  unfold tailWord_1969322
  simp only [CollatzResearch.WordTrace]
  refine ⟨17956768542872550566459555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47884716114326801510558813 17956768542872550566459555)
  ·
    refine ⟨26935152814308825849689333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17956768542872550566459555 26935152814308825849689333)
    ·
      refine ⟨2525170576341452423408375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26935152814308825849689333 2525170576341452423408375)
      ·
        refine ⟨3787755864512178635112563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525170576341452423408375 3787755864512178635112563)
        ·
          refine ⟨5681633796768267952668845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787755864512178635112563 5681633796768267952668845)
          ·
            refine ⟨2130612673788100482250817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5681633796768267952668845 2130612673788100482250817)
            ·
              refine ⟨1597959505341075361688113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2130612673788100482250817 1597959505341075361688113)
              ·
                refine ⟨1198469629005806521266085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1597959505341075361688113 1198469629005806521266085)
                ·
                  refine ⟨224713055438588722737391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1198469629005806521266085 224713055438588722737391)
                  ·
                    rfl

theorem cell22_1969322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_1969322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969322 prefixEnd_1969322 := by exact prefixLift 1969322
  have htrace : WordTrace (prefixWord ++ tailWord_1969322) baseStart_1969322 baseEnd_1969322 := by
    simpa [prefixWord, tailWord_1969322, baseEnd_1969322] using wordTrace_append hprefix tailTrace_1969322
  have hstable : (prefixWord ++ tailWord_1969322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969322).length < 2 ^ (prefixWord ++ tailWord_1969322).sum := by decide
  have hdescent : baseEnd_1969322 < baseStart_1969322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969365 : List Nat := [1, 3, 2, 4, 1, 1, 1, 5, 1, 3]
def baseStart_1969365 : Nat := 118140960795 + 1969365 * 2 ^ 59
def prefixEnd_1969365 : Nat := 4983230072969 + 3 ^ 40 * 1969365 * 2
def baseEnd_1969365 : Nat := 674153886094528389387041

theorem tailTrace_1969365 : CollatzResearch.WordTrace tailWord_1969365 prefixEnd_1969365 674153886094528389387041 := by
  unfold tailWord_1969365
  simp only [CollatzResearch.WordTrace]
  refine ⟨71828642510334420609653549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47885761673556280406435699 71828642510334420609653549)
  ·
    refine ⟨26935740941375407728620081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71828642510334420609653549 26935740941375407728620081)
    ·
      refine ⟨20201805706031555796465061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26935740941375407728620081 20201805706031555796465061)
      ·
        refine ⟨3787838569880916711837199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20201805706031555796465061 3787838569880916711837199)
        ·
          refine ⟨5681757854821375067755799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3787838569880916711837199 5681757854821375067755799)
          ·
            refine ⟨8522636782232062601633699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5681757854821375067755799 8522636782232062601633699)
            ·
              refine ⟨12783955173348093902450549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8522636782232062601633699 12783955173348093902450549)
              ·
                refine ⟨1198495797501383803354739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12783955173348093902450549 1198495797501383803354739)
                ·
                  refine ⟨1797743696252075705032109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198495797501383803354739 1797743696252075705032109)
                  ·
                    refine ⟨674153886094528389387041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1797743696252075705032109 674153886094528389387041)
                    ·
                      rfl

theorem cell22_1969365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_1969365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969365 prefixEnd_1969365 := by exact prefixLift 1969365
  have htrace : WordTrace (prefixWord ++ tailWord_1969365) baseStart_1969365 baseEnd_1969365 := by
    simpa [prefixWord, tailWord_1969365, baseEnd_1969365] using wordTrace_append hprefix tailTrace_1969365
  have hstable : (prefixWord ++ tailWord_1969365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969365).length < 2 ^ (prefixWord ++ tailWord_1969365).sum := by decide
  have hdescent : baseEnd_1969365 < baseStart_1969365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969436 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_1969436 : Nat := 118140960795 + 1969436 * 2 ^ 59
def prefixEnd_1969436 : Nat := 4983230072969 + 3 ^ 40 * 1969436 * 2
def baseEnd_1969436 : Nat := 674178190845507870861823

theorem tailTrace_1969436 : CollatzResearch.WordTrace tailWord_1969436 prefixEnd_1969436 674178190845507870861823 := by
  unfold tailWord_1969436
  simp only [CollatzResearch.WordTrace]
  refine ⟨35915616046538599867744081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47887488062051466490325441 35915616046538599867744081)
  ·
    refine ⟨26936712034903949900808061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35915616046538599867744081 26936712034903949900808061)
    ·
      refine ⟨10101267013088981212803023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26936712034903949900808061 10101267013088981212803023)
      ·
        refine ⟨15151900519633471819204535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10101267013088981212803023 15151900519633471819204535)
        ·
          refine ⟨22727850779450207728806803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15151900519633471819204535 22727850779450207728806803)
          ·
            refine ⟨34091776169175311593210205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22727850779450207728806803 34091776169175311593210205)
            ·
              refine ⟨12784416063440741847453827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34091776169175311593210205 12784416063440741847453827)
              ·
                refine ⟨19176624095161112771180741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12784416063440741847453827 19176624095161112771180741)
                ·
                  refine ⟨3595617017842708644596389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19176624095161112771180741 3595617017842708644596389)
                  ·
                    refine ⟨674178190845507870861823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3595617017842708644596389 674178190845507870861823)
                    ·
                      rfl

theorem cell22_1969436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_1969436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969436 prefixEnd_1969436 := by exact prefixLift 1969436
  have htrace : WordTrace (prefixWord ++ tailWord_1969436) baseStart_1969436 baseEnd_1969436 := by
    simpa [prefixWord, tailWord_1969436, baseEnd_1969436] using wordTrace_append hprefix tailTrace_1969436
  have hstable : (prefixWord ++ tailWord_1969436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969436).length < 2 ^ (prefixWord ++ tailWord_1969436).sum := by decide
  have hdescent : baseEnd_1969436 < baseStart_1969436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969440 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 6]
def baseStart_1969440 : Nat := 118140960795 + 1969440 * 2 ^ 59
def prefixEnd_1969440 : Nat := 4983230072969 + 3 ^ 40 * 1969440 * 2
def baseEnd_1969440 : Nat := 224726520042417731253937

theorem tailTrace_1969440 : CollatzResearch.WordTrace tailWord_1969440 prefixEnd_1969440 224726520042417731253937 := by
  unfold tailWord_1969440
  simp only [CollatzResearch.WordTrace]
  refine ⟨35915688992531354209316887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47887585323375138945755849 35915688992531354209316887)
  ·
    refine ⟨53873533488797031313975331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35915688992531354209316887 53873533488797031313975331)
    ·
      refine ⟨80810300233195546970962997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53873533488797031313975331 80810300233195546970962997)
      ·
        refine ⟨7575965646862082528527781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80810300233195546970962997 7575965646862082528527781)
        ·
          refine ⟨1420493558786640474098959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7575965646862082528527781 1420493558786640474098959)
          ·
            refine ⟨2130740338179960711148439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420493558786640474098959 2130740338179960711148439)
            ·
              refine ⟨3196110507269941066722659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2130740338179960711148439 3196110507269941066722659)
              ·
                refine ⟨4794165760904911600083989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3196110507269941066722659 4794165760904911600083989)
                ·
                  refine ⟨224726520042417731253937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4794165760904911600083989 224726520042417731253937)
                  ·
                    rfl

theorem cell22_1969440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 6].length) (baseStart_1969440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969440 prefixEnd_1969440 := by exact prefixLift 1969440
  have htrace : WordTrace (prefixWord ++ tailWord_1969440) baseStart_1969440 baseEnd_1969440 := by
    simpa [prefixWord, tailWord_1969440, baseEnd_1969440] using wordTrace_append hprefix tailTrace_1969440
  have hstable : (prefixWord ++ tailWord_1969440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969440).length < 2 ^ (prefixWord ++ tailWord_1969440).sum := by decide
  have hdescent : baseEnd_1969440 < baseStart_1969440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969449 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 3, 9]
def baseStart_1969449 : Nat := 118140960795 + 1969449 * 2 ^ 59
def prefixEnd_1969449 : Nat := 4983230072969 + 3 ^ 40 * 1969449 * 2
def baseEnd_1969449 : Nat := 674182641011180170286783

theorem tailTrace_1969449 : CollatzResearch.WordTrace tailWord_1969449 prefixEnd_1969449 674182641011180170286783 := by
  unfold tailWord_1969449
  simp only [CollatzResearch.WordTrace]
  refine ⟨71831706242030102955711401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47887804161353401970474267 71831706242030102955711401)
  ·
    refine ⟨53873779681522577216783551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71831706242030102955711401 53873779681522577216783551)
    ·
      refine ⟨80810669522283865825175327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53873779681522577216783551 80810669522283865825175327)
      ·
        refine ⟨121216004283425798737762991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80810669522283865825175327 121216004283425798737762991)
        ·
          refine ⟨181824006425138698106644487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121216004283425798737762991 181824006425138698106644487)
          ·
            refine ⟨272736009637708047159966731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181824006425138698106644487 272736009637708047159966731)
            ·
              refine ⟨409104014456562070739950097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272736009637708047159966731 409104014456562070739950097)
              ·
                refine ⟨306828010842421553054962573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409104014456562070739950097 306828010842421553054962573)
                ·
                  refine ⟨115060504065908082395610965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 306828010842421553054962573 115060504065908082395610965)
                  ·
                    refine ⟨674182641011180170286783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 115060504065908082395610965 674182641011180170286783)
                    ·
                      rfl

theorem cell22_1969449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_1969449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969449 prefixEnd_1969449 := by exact prefixLift 1969449
  have htrace : WordTrace (prefixWord ++ tailWord_1969449) baseStart_1969449 baseEnd_1969449 := by
    simpa [prefixWord, tailWord_1969449, baseEnd_1969449] using wordTrace_append hprefix tailTrace_1969449
  have hstable : (prefixWord ++ tailWord_1969449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969449).length < 2 ^ (prefixWord ++ tailWord_1969449).sum := by decide
  have hdescent : baseEnd_1969449 < baseStart_1969449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969485 : List Nat := [1, 6, 1, 3, 2, 9]
def baseStart_1969485 : Nat := 118140960795 + 1969485 * 2 ^ 59
def prefixEnd_1969485 : Nat := 4983230072969 + 3 ^ 40 * 1969485 * 2
def baseEnd_1969485 : Nat := 8323394624035655264033

theorem tailTrace_1969485 : CollatzResearch.WordTrace tailWord_1969485 prefixEnd_1969485 8323394624035655264033 := by
  unfold tailWord_1969485
  simp only [CollatzResearch.WordTrace]
  refine ⟨71833019269899681104021909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47888679513266454069347939 71833019269899681104021909)
  ·
    refine ⟨3367172778276547551751027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71833019269899681104021909 3367172778276547551751027)
    ·
      refine ⟨5050759167414821327626541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3367172778276547551751027 5050759167414821327626541)
      ·
        refine ⟨1894034687780557997859953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5050759167414821327626541 1894034687780557997859953)
        ·
          refine ⟨1420526015835418498394965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1894034687780557997859953 1420526015835418498394965)
          ·
            refine ⟨8323394624035655264033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1420526015835418498394965 8323394624035655264033)
            ·
              rfl

theorem cell22_1969485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 9].length) (baseStart_1969485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969485 prefixEnd_1969485 := by exact prefixLift 1969485
  have htrace : WordTrace (prefixWord ++ tailWord_1969485) baseStart_1969485 baseEnd_1969485 := by
    simpa [prefixWord, tailWord_1969485, baseEnd_1969485] using wordTrace_append hprefix tailTrace_1969485
  have hstable : (prefixWord ++ tailWord_1969485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969485).length < 2 ^ (prefixWord ++ tailWord_1969485).sum := by decide
  have hdescent : baseEnd_1969485 < baseStart_1969485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969571 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 3, 6]
def baseStart_1969571 : Nat := 118140960795 + 1969571 * 2 ^ 59
def prefixEnd_1969571 : Nat := 4983230072969 + 3 ^ 40 * 1969571 * 2
def baseEnd_1969571 : Nat := 674224404104412518736409

theorem tailTrace_1969571 : CollatzResearch.WordTrace tailWord_1969571 prefixEnd_1969571 674224404104412518736409 := by
  unfold tailWord_1969571
  simp only [CollatzResearch.WordTrace]
  refine ⟨71836155947588117791652567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47890770631725411861101711 71836155947588117791652567)
  ·
    refine ⟨107754233921382176687478851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71836155947588117791652567 107754233921382176687478851)
    ·
      refine ⟨161631350882073265031218277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107754233921382176687478851 161631350882073265031218277)
      ·
        refine ⟨30305878290388737193353427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 161631350882073265031218277 30305878290388737193353427)
        ·
          refine ⟨45458817435583105790030141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30305878290388737193353427 45458817435583105790030141)
          ·
            refine ⟨17047056538343664671261303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45458817435583105790030141 17047056538343664671261303)
            ·
              refine ⟨25570584807515497006891955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17047056538343664671261303 25570584807515497006891955)
              ·
                refine ⟨38355877211273245510337933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25570584807515497006891955 38355877211273245510337933)
                ·
                  refine ⟨14383453954227467066376725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38355877211273245510337933 14383453954227467066376725)
                  ·
                    refine ⟨674224404104412518736409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14383453954227467066376725 674224404104412518736409)
                    ·
                      rfl

theorem cell22_1969571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 6].length) (baseStart_1969571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969571 prefixEnd_1969571 := by exact prefixLift 1969571
  have htrace : WordTrace (prefixWord ++ tailWord_1969571) baseStart_1969571 baseEnd_1969571 := by
    simpa [prefixWord, tailWord_1969571, baseEnd_1969571] using wordTrace_append hprefix tailTrace_1969571
  have hstable : (prefixWord ++ tailWord_1969571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969571).length < 2 ^ (prefixWord ++ tailWord_1969571).sum := by decide
  have hdescent : baseEnd_1969571 < baseStart_1969571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969616 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 1, 8]
def baseStart_1969616 : Nat := 118140960795 + 1969616 * 2 ^ 59
def prefixEnd_1969616 : Nat := 4983230072969 + 3 ^ 40 * 1969616 * 2
def baseEnd_1969616 : Nat := 674239808524047401361271

theorem tailTrace_1969616 : CollatzResearch.WordTrace tailWord_1969616 prefixEnd_1969616 674239808524047401361271 := by
  unfold tailWord_1969616
  simp only [CollatzResearch.WordTrace]
  refine ⟨35918898616212545238520351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47891864821616726984693801 35918898616212545238520351)
  ·
    refine ⟨53878347924318817857780527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35918898616212545238520351 53878347924318817857780527)
    ·
      refine ⟨80817521886478226786670791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53878347924318817857780527 80817521886478226786670791)
      ·
        refine ⟨121226282829717340180006187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80817521886478226786670791 121226282829717340180006187)
        ·
          refine ⟨181839424244576010270009281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121226282829717340180006187 181839424244576010270009281)
          ·
            refine ⟨136379568183432007702506961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181839424244576010270009281 136379568183432007702506961)
            ·
              refine ⟨102284676137574005776880221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 136379568183432007702506961 102284676137574005776880221)
              ·
                refine ⟨38356753551590252166330083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 102284676137574005776880221 38356753551590252166330083)
                ·
                  refine ⟨57535130327385378249495125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38356753551590252166330083 57535130327385378249495125)
                  ·
                    refine ⟨674239808524047401361271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57535130327385378249495125 674239808524047401361271)
                    ·
                      rfl

theorem cell22_1969616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_1969616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969616 prefixEnd_1969616 := by exact prefixLift 1969616
  have htrace : WordTrace (prefixWord ++ tailWord_1969616) baseStart_1969616 baseEnd_1969616 := by
    simpa [prefixWord, tailWord_1969616, baseEnd_1969616] using wordTrace_append hprefix tailTrace_1969616
  have hstable : (prefixWord ++ tailWord_1969616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969616).length < 2 ^ (prefixWord ++ tailWord_1969616).sum := by decide
  have hdescent : baseEnd_1969616 < baseStart_1969616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969620 : List Nat := [2, 4, 1, 2, 3, 1, 2, 7]
def baseStart_1969620 : Nat := 118140960795 + 1969620 * 2 ^ 59
def prefixEnd_1969620 : Nat := 4983230072969 + 3 ^ 40 * 1969620 * 2
def baseEnd_1969620 : Nat := 74915686422865858251251

theorem tailTrace_1969620 : CollatzResearch.WordTrace tailWord_1969620 prefixEnd_1969620 74915686422865858251251 := by
  unfold tailWord_1969620
  simp only [CollatzResearch.WordTrace]
  refine ⟨35918971562205299580093157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47891962082940399440124209 35918971562205299580093157)
  ·
    refine ⟨6734807167913493671267467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35918971562205299580093157 6734807167913493671267467)
    ·
      refine ⟨10102210751870240506901201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6734807167913493671267467 10102210751870240506901201)
      ·
        refine ⟨7576658063902680380175901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10102210751870240506901201 7576658063902680380175901)
        ·
          refine ⟨2841246773963505142565963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7576658063902680380175901 2841246773963505142565963)
          ·
            refine ⟨4261870160945257713848945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841246773963505142565963 4261870160945257713848945)
            ·
              refine ⟨3196402620708943285386709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4261870160945257713848945 3196402620708943285386709)
              ·
                refine ⟨74915686422865858251251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3196402620708943285386709 74915686422865858251251)
                ·
                  rfl

theorem cell22_1969620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 7].length) (baseStart_1969620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969620 prefixEnd_1969620 := by exact prefixLift 1969620
  have htrace : WordTrace (prefixWord ++ tailWord_1969620) baseStart_1969620 baseEnd_1969620 := by
    simpa [prefixWord, tailWord_1969620, baseEnd_1969620] using wordTrace_append hprefix tailTrace_1969620
  have hstable : (prefixWord ++ tailWord_1969620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969620).length < 2 ^ (prefixWord ++ tailWord_1969620).sum := by decide
  have hdescent : baseEnd_1969620 < baseStart_1969620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969738 : List Nat := [3, 1, 2, 1, 1, 3, 2, 9]
def baseStart_1969738 : Nat := 118140960795 + 1969738 * 2 ^ 59
def prefixEnd_1969738 : Nat := 4983230072969 + 3 ^ 40 * 1969738 * 2
def baseEnd_1969738 : Nat := 74920174624142194423433

theorem tailTrace_1969738 : CollatzResearch.WordTrace tailWord_1969738 prefixEnd_1969738 74920174624142194423433 := by
  unfold tailWord_1969738
  simp only [CollatzResearch.WordTrace]
  refine ⟨17960561734495776328245467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47894831291988736875321245 17960561734495776328245467)
  ·
    refine ⟨26940842601743664492368201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17960561734495776328245467 26940842601743664492368201)
    ·
      refine ⟨20205631951307748369276151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26940842601743664492368201 20205631951307748369276151)
      ·
        refine ⟨30308447926961622553914227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20205631951307748369276151 30308447926961622553914227)
        ·
          refine ⟨45462671890442433830871341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30308447926961622553914227 45462671890442433830871341)
          ·
            refine ⟨17048501958915912686576753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45462671890442433830871341 17048501958915912686576753)
            ·
              refine ⟨12786376469186934514932565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17048501958915912686576753 12786376469186934514932565)
              ·
                refine ⟨74920174624142194423433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12786376469186934514932565 74920174624142194423433)
                ·
                  rfl

theorem cell22_1969738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 9].length) (baseStart_1969738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969738 prefixEnd_1969738 := by exact prefixLift 1969738
  have htrace : WordTrace (prefixWord ++ tailWord_1969738) baseStart_1969738 baseEnd_1969738 := by
    simpa [prefixWord, tailWord_1969738, baseEnd_1969738] using wordTrace_append hprefix tailTrace_1969738
  have hstable : (prefixWord ++ tailWord_1969738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969738).length < 2 ^ (prefixWord ++ tailWord_1969738).sum := by decide
  have hdescent : baseEnd_1969738 < baseStart_1969738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969838 : List Nat := [4, 1, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1969838 : Nat := 118140960795 + 1969838 * 2 ^ 59
def prefixEnd_1969838 : Nat := 4983230072969 + 3 ^ 40 * 1969838 * 2
def baseEnd_1969838 : Nat := 674315803660912822310591

theorem tailTrace_1969838 : CollatzResearch.WordTrace tailWord_1969838 prefixEnd_1969838 674315803660912822310591 := by
  unfold tailWord_1969838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8980736779702602798952771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47897262825080548261081445 8980736779702602798952771)
  ·
    refine ⟨13471105169553904198429157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8980736779702602798952771 13471105169553904198429157)
    ·
      refine ⟨2525832219291357037205467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13471105169553904198429157 2525832219291357037205467)
      ·
        refine ⟨3788748328937035555808201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2525832219291357037205467 3788748328937035555808201)
        ·
          refine ⟨2841561246702776666856151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3788748328937035555808201 2841561246702776666856151)
          ·
            refine ⟨4262341870054165000284227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2841561246702776666856151 4262341870054165000284227)
            ·
              refine ⟨6393512805081247500426341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4262341870054165000284227 6393512805081247500426341)
              ·
                refine ⟨1198783650952733906329939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6393512805081247500426341 1198783650952733906329939)
                ·
                  refine ⟨1798175476429100859494909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198783650952733906329939 1798175476429100859494909)
                  ·
                    refine ⟨674315803660912822310591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1798175476429100859494909 674315803660912822310591)
                    ·
                      rfl

theorem cell22_1969838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1969838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969838 prefixEnd_1969838 := by exact prefixLift 1969838
  have htrace : WordTrace (prefixWord ++ tailWord_1969838) baseStart_1969838 baseEnd_1969838 := by
    simpa [prefixWord, tailWord_1969838, baseEnd_1969838] using wordTrace_append hprefix tailTrace_1969838
  have hstable : (prefixWord ++ tailWord_1969838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969838).length < 2 ^ (prefixWord ++ tailWord_1969838).sum := by decide
  have hdescent : baseEnd_1969838 < baseStart_1969838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969922 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1969922 : Nat := 118140960795 + 1969922 * 2 ^ 59
def prefixEnd_1969922 : Nat := 4983230072969 + 3 ^ 40 * 1969922 * 2
def baseEnd_1969922 : Nat := 674344558577564603210333

theorem tailTrace_1969922 : CollatzResearch.WordTrace tailWord_1969922 prefixEnd_1969922 674344558577564603210333 := by
  unfold tailWord_1969922
  simp only [CollatzResearch.WordTrace]
  refine ⟨17962239492329126184420005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47899305312877669825120013 17962239492329126184420005)
  ·
    refine ⟨3367919904811711159578751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17962239492329126184420005 3367919904811711159578751)
    ·
      refine ⟨5051879857217566739368127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3367919904811711159578751 5051879857217566739368127)
      ·
        refine ⟨7577819785826350109052191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5051879857217566739368127 7577819785826350109052191)
        ·
          refine ⟨11366729678739525163578287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7577819785826350109052191 11366729678739525163578287)
          ·
            refine ⟨17050094518109287745367431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11366729678739525163578287 17050094518109287745367431)
            ·
              refine ⟨25575141777163931618051147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17050094518109287745367431 25575141777163931618051147)
              ·
                refine ⟨38362712665745897427076721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25575141777163931618051147 38362712665745897427076721)
                ·
                  refine ⟨28772034499309423070307541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38362712665745897427076721 28772034499309423070307541)
                  ·
                    refine ⟨674344558577564603210333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28772034499309423070307541 674344558577564603210333)
                    ·
                      rfl

theorem cell22_1969922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1969922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969922 prefixEnd_1969922 := by exact prefixLift 1969922
  have htrace : WordTrace (prefixWord ++ tailWord_1969922) baseStart_1969922 baseEnd_1969922 := by
    simpa [prefixWord, tailWord_1969922, baseEnd_1969922] using wordTrace_append hprefix tailTrace_1969922
  have hstable : (prefixWord ++ tailWord_1969922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969922).length < 2 ^ (prefixWord ++ tailWord_1969922).sum := by decide
  have hdescent : baseEnd_1969922 < baseStart_1969922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969924 : List Nat := [2, 3, 2, 2, 1, 4, 2, 6]
def baseStart_1969924 : Nat := 118140960795 + 1969924 * 2 ^ 59
def prefixEnd_1969924 : Nat := 4983230072969 + 3 ^ 40 * 1969924 * 2
def baseEnd_1969924 : Nat := 74927249246493029406703

theorem tailTrace_1969924 : CollatzResearch.WordTrace tailWord_1969924 prefixEnd_1969924 74927249246493029406703 := by
  unfold tailWord_1969924
  simp only [CollatzResearch.WordTrace]
  refine ⟨35924515457654629539626413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47899353943539506052835217 35924515457654629539626413)
  ·
    refine ⟨13471693296620486077359905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35924515457654629539626413 13471693296620486077359905)
    ·
      refine ⟨10103769972465364558019929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13471693296620486077359905 10103769972465364558019929)
      ·
        refine ⟨7577827479349023418514947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10103769972465364558019929 7577827479349023418514947)
        ·
          refine ⟨11366741219023535127772421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7577827479349023418514947 11366741219023535127772421)
          ·
            refine ⟨2131263978566912836457329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11366741219023535127772421 2131263978566912836457329)
            ·
              refine ⟨1598447983925184627342997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2131263978566912836457329 1598447983925184627342997)
              ·
                refine ⟨74927249246493029406703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1598447983925184627342997 74927249246493029406703)
                ·
                  rfl

theorem cell22_1969924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 6].length) (baseStart_1969924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969924 prefixEnd_1969924 := by exact prefixLift 1969924
  have htrace : WordTrace (prefixWord ++ tailWord_1969924) baseStart_1969924 baseEnd_1969924 := by
    simpa [prefixWord, tailWord_1969924, baseEnd_1969924] using wordTrace_append hprefix tailTrace_1969924
  have hstable : (prefixWord ++ tailWord_1969924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969924).length < 2 ^ (prefixWord ++ tailWord_1969924).sum := by decide
  have hdescent : baseEnd_1969924 < baseStart_1969924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969939 : List Nat := [1, 1, 1, 2, 1, 3, 2, 7, 1, 3]
def baseStart_1969939 : Nat := 118140960795 + 1969939 * 2 ^ 59
def prefixEnd_1969939 : Nat := 4983230072969 + 3 ^ 40 * 1969939 * 2
def baseEnd_1969939 : Nat := 674350378024982225535281

theorem tailTrace_1969939 : CollatzResearch.WordTrace tailWord_1969939 prefixEnd_1969939 674350378024982225535281 := by
  unfold tailWord_1969939
  simp only [CollatzResearch.WordTrace]
  refine ⟨71849578010254916641048871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47899718673503277760699247 71849578010254916641048871)
  ·
    refine ⟨107774367015382374961573307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71849578010254916641048871 107774367015382374961573307)
    ·
      refine ⟨161661550523073562442359961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107774367015382374961573307 161661550523073562442359961)
      ·
        refine ⟨121246162892305171831769971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 161661550523073562442359961 121246162892305171831769971)
        ·
          refine ⟨181869244338457757747654957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121246162892305171831769971 181869244338457757747654957)
          ·
            refine ⟨68200966626921659155370609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 181869244338457757747654957 68200966626921659155370609)
            ·
              refine ⟨51150724970191244366527957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68200966626921659155370609 51150724970191244366527957)
              ·
                refine ⟨1198845116488857289840499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 51150724970191244366527957 1198845116488857289840499)
                ·
                  refine ⟨1798267674733285934760749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1198845116488857289840499 1798267674733285934760749)
                  ·
                    refine ⟨674350378024982225535281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1798267674733285934760749 674350378024982225535281)
                    ·
                      rfl

theorem cell22_1969939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 1, 3].length) (baseStart_1969939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969939 prefixEnd_1969939 := by exact prefixLift 1969939
  have htrace : WordTrace (prefixWord ++ tailWord_1969939) baseStart_1969939 baseEnd_1969939 := by
    simpa [prefixWord, tailWord_1969939, baseEnd_1969939] using wordTrace_append hprefix tailTrace_1969939
  have hstable : (prefixWord ++ tailWord_1969939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969939).length < 2 ^ (prefixWord ++ tailWord_1969939).sum := by decide
  have hdescent : baseEnd_1969939 < baseStart_1969939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969952 : List Nat := [2, 1, 1, 5, 1, 1, 2, 4, 5]
def baseStart_1969952 : Nat := 118140960795 + 1969952 * 2 ^ 59
def prefixEnd_1969952 : Nat := 4983230072969 + 3 ^ 40 * 1969952 * 2
def baseEnd_1969952 : Nat := 224784942730218174986747

theorem tailTrace_1969952 : CollatzResearch.WordTrace tailWord_1969952 prefixEnd_1969952 224784942730218174986747 := by
  unfold tailWord_1969952
  simp only [CollatzResearch.WordTrace]
  refine ⟨35925026079603909930636055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47900034772805213240848073 35925026079603909930636055)
  ·
    refine ⟨53887539119405864895954083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35925026079603909930636055 53887539119405864895954083)
    ·
      refine ⟨80831308679108797343931125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53887539119405864895954083 80831308679108797343931125)
      ·
        refine ⟨7577935188666449750993543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80831308679108797343931125 7577935188666449750993543)
        ·
          refine ⟨11366902782999674626490315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7577935188666449750993543 11366902782999674626490315)
          ·
            refine ⟨17050354174499511939735473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11366902782999674626490315 17050354174499511939735473)
            ·
              refine ⟨12787765630874633954801605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17050354174499511939735473 12787765630874633954801605)
              ·
                refine ⟨2397706055788993866525301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12787765630874633954801605 2397706055788993866525301)
                ·
                  refine ⟨224784942730218174986747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2397706055788993866525301 224784942730218174986747)
                  ·
                    rfl

theorem cell22_1969952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 5].length) (baseStart_1969952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969952 prefixEnd_1969952 := by exact prefixLift 1969952
  have htrace : WordTrace (prefixWord ++ tailWord_1969952) baseStart_1969952 baseEnd_1969952 := by
    simpa [prefixWord, tailWord_1969952, baseEnd_1969952] using wordTrace_append hprefix tailTrace_1969952
  have hstable : (prefixWord ++ tailWord_1969952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969952).length < 2 ^ (prefixWord ++ tailWord_1969952).sum := by decide
  have hdescent : baseEnd_1969952 < baseStart_1969952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969956 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_1969956 : Nat := 118140960795 + 1969956 * 2 ^ 59
def prefixEnd_1969956 : Nat := 4983230072969 + 3 ^ 40 * 1969956 * 2
def baseEnd_1969956 : Nat := 674356197472399847860229

theorem tailTrace_1969956 : CollatzResearch.WordTrace tailWord_1969956 prefixEnd_1969956 674356197472399847860229 := by
  unfold tailWord_1969956
  simp only [CollatzResearch.WordTrace]
  refine ⟨35925099025596664272208861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47900132034128885696278481 35925099025596664272208861)
  ·
    refine ⟨13471912134598749102078323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35925099025596664272208861 13471912134598749102078323)
    ·
      refine ⟨20207868201898123653117485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13471912134598749102078323 20207868201898123653117485)
      ·
        refine ⟨7577950575711796369919057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20207868201898123653117485 7577950575711796369919057)
        ·
          refine ⟨5683462931783847277439293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7577950575711796369919057 5683462931783847277439293)
          ·
            refine ⟨2131298599418942729039735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5683462931783847277439293 2131298599418942729039735)
            ·
              refine ⟨3196947899128414093559603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2131298599418942729039735 3196947899128414093559603)
              ·
                refine ⟨4795421848692621140339405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3196947899128414093559603 4795421848692621140339405)
                ·
                  refine ⟨1798283193259732927627277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4795421848692621140339405 1798283193259732927627277)
                  ·
                    refine ⟨674356197472399847860229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1798283193259732927627277 674356197472399847860229)
                    ·
                      rfl

theorem cell22_1969956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_1969956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969956 prefixEnd_1969956 := by exact prefixLift 1969956
  have htrace : WordTrace (prefixWord ++ tailWord_1969956) baseStart_1969956 baseEnd_1969956 := by
    simpa [prefixWord, tailWord_1969956, baseEnd_1969956] using wordTrace_append hprefix tailTrace_1969956
  have hstable : (prefixWord ++ tailWord_1969956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969956).length < 2 ^ (prefixWord ++ tailWord_1969956).sum := by decide
  have hdescent : baseEnd_1969956 < baseStart_1969956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1969969 : List Nat := [1, 2, 2, 3, 2, 2, 4, 1, 5]
def baseStart_1969969 : Nat := 118140960795 + 1969969 * 2 ^ 59
def prefixEnd_1969969 : Nat := 4983230072969 + 3 ^ 40 * 1969969 * 2
def baseEnd_1969969 : Nat := 224786882546024049095063

theorem tailTrace_1969969 : CollatzResearch.WordTrace tailWord_1969969 prefixEnd_1969969 224786882546024049095063 := by
  unfold tailWord_1969969
  simp only [CollatzResearch.WordTrace]
  refine ⟨71850672200146231764640961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47900448133430821176427307 71850672200146231764640961)
  ·
    refine ⟨53888004150109673823480721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71850672200146231764640961 53888004150109673823480721)
    ·
      refine ⟨40416003112582255367610541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53888004150109673823480721 40416003112582255367610541)
      ·
        refine ⟨15156001167218345762853953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40416003112582255367610541 15156001167218345762853953)
        ·
          refine ⟨11367000875413759322140465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15156001167218345762853953 11367000875413759322140465)
          ·
            refine ⟨8525250656560319491605349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11367000875413759322140465 8525250656560319491605349)
            ·
              refine ⟨1598484498105059904676003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8525250656560319491605349 1598484498105059904676003)
              ·
                refine ⟨2397726747157589857014005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1598484498105059904676003 2397726747157589857014005)
                ·
                  refine ⟨224786882546024049095063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2397726747157589857014005 224786882546024049095063)
                  ·
                    rfl

theorem cell22_1969969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 5].length) (baseStart_1969969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1969969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1969969 prefixEnd_1969969 := by exact prefixLift 1969969
  have htrace : WordTrace (prefixWord ++ tailWord_1969969) baseStart_1969969 baseEnd_1969969 := by
    simpa [prefixWord, tailWord_1969969, baseEnd_1969969] using wordTrace_append hprefix tailTrace_1969969
  have hstable : (prefixWord ++ tailWord_1969969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1969969).length < 2 ^ (prefixWord ++ tailWord_1969969).sum := by decide
  have hdescent : baseEnd_1969969 < baseStart_1969969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1969969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1970046 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1970046 : Nat := 118140960795 + 1970046 * 2 ^ 59
def prefixEnd_1970046 : Nat := 4983230072969 + 3 ^ 40 * 1970046 * 2
def baseEnd_1970046 : Nat := 674387006311669613109953

theorem tailTrace_1970046 : CollatzResearch.WordTrace tailWord_1970046 prefixEnd_1970046 674387006311669613109953 := by
  unfold tailWord_1970046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8981685077608409239399249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47902320413911515943462661 8981685077608409239399249)
  ·
    refine ⟨6736263808206306929549437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8981685077608409239399249 6736263808206306929549437)
    ·
      refine ⟨2526098928077365098581039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6736263808206306929549437 2526098928077365098581039)
      ·
        refine ⟨3789148392116047647871559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2526098928077365098581039 3789148392116047647871559)
        ·
          refine ⟨5683722588174071471807339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3789148392116047647871559 5683722588174071471807339)
          ·
            refine ⟨8525583882261107207711009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5683722588174071471807339 8525583882261107207711009)
            ·
              refine ⟨6394187911695830405783257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8525583882261107207711009 6394187911695830405783257)
              ·
                refine ⟨4795640933771872804337443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6394187911695830405783257 4795640933771872804337443)
                ·
                  refine ⟨7193461400657809206506165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4795640933771872804337443 7193461400657809206506165)
                  ·
                    refine ⟨674387006311669613109953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7193461400657809206506165 674387006311669613109953)
                    ·
                      rfl

theorem cell22_1970046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1970046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1970046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1970046 prefixEnd_1970046 := by exact prefixLift 1970046
  have htrace : WordTrace (prefixWord ++ tailWord_1970046) baseStart_1970046 baseEnd_1970046 := by
    simpa [prefixWord, tailWord_1970046, baseEnd_1970046] using wordTrace_append hprefix tailTrace_1970046
  have hstable : (prefixWord ++ tailWord_1970046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1970046).length < 2 ^ (prefixWord ++ tailWord_1970046).sum := by decide
  have hdescent : baseEnd_1970046 < baseStart_1970046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1970046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
